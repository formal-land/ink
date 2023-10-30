// our modifications:

use derive_more::From;

#[cfg(any(feature = "std", test, doc))]
use crate::engine::off_chain::OffChainError;

use crate::engine::EnvInstance;
use core::fmt::Debug;
use ink_engine::test_api::RecordedDebugMessages;
use std::panic::UnwindSafe;

use crate::{
    call::{
        ConstructorReturnType,
        CreateParams,
        FromAccountId,
    },
    hash::{
        CryptoHash,
        HashOutput,
    },
    topics::Topics,
    Environment,
};
use ink_storage_traits::Storable;

use crate::{
    Error as EnvError,
    Result as EnvResult,
};
use ink_primitives::{
    ConstructorResult,
    LangError,
};

use crate::{
    call::{
        utils::{
            EmptyArgumentList,
            ReturnType,
            Set,
            Unset,
        },
        ExecutionInput,
    },
    types::Gas,
};
use core::marker::PhantomData;
use num_traits::Zero;

// from error.rs
/// Errors that can be encountered upon environmental interaction.
#[derive(Debug, From, PartialEq, Eq)]
pub enum Error {
    /// Error upon decoding an encoded value.
    Decode(scale::Error),
    /// An error that can only occur in the off-chain environment.
    #[cfg(any(feature = "std", test, doc))]
    OffChain(OffChainError),
    /// The call to another contract has trapped.
    CalleeTrapped,
    /// The call to another contract has been reverted.
    CalleeReverted,
    /// The queried contract storage entry is missing.
    KeyNotFound,
    /// Deprecated and no longer returned: There is only the minimum balance.
    _BelowSubsistenceThreshold,
    /// Transfer failed for other not further specified reason. Most probably
    /// reserved or locked balance of the sender that was preventing the transfer.
    TransferFailed,
    /// Deprecated and no longer returned: Endowment is no longer required.
    _EndowmentTooLow,
    /// No code could be found at the supplied code hash.
    CodeNotFound,
    /// The account that was called is no contract, but a plain account.
    NotCallable,
    /// An unknown error has occurred.
    Unknown,
    /// The call to `debug_message` had no effect because debug message
    /// recording was disabled.
    LoggingDisabled,
    /// The call dispatched by `call_runtime` was executed but returned an error.
    CallRuntimeFailed,
    /// ECDSA pubkey recovery failed. Most probably wrong recovery id or signature.
    EcdsaRecoveryFailed,
}

/// A result of environmental operations.
pub type Result<T> = core::result::Result<T, Error>;

// from engine/off_chain/test_api.rs:
/// Record for an emitted event.
#[derive(Clone)]
pub struct EmittedEvent {
    /// Recorded topics of the emitted event.
    pub topics: Vec<Vec<u8>>,
    /// Recorded encoding of the emitted event.
    pub data: Vec<u8>,
}

/// Sets the balance of the account to the given balance.
///
/// # Note
///
/// Note that account could refer to either a user account or
/// a smart contract account.
///
/// # Errors
///
/// - If `account` does not exist.
/// - If the underlying `account` type does not match.
/// - If the underlying `new_balance` type does not match.
pub fn set_account_balance<T>(account_id: T::AccountId, new_balance: T::Balance)
where
    T: Environment<Balance = u128>, // Just temporary for the MVP!
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .set_balance(scale::Encode::encode(&account_id), new_balance);
    })
}

/// Returns the balance of the account.
///
/// # Note
///
/// Note that account could refer to either a user account or
/// a smart contract account. This returns the same as `env::api::balance`
/// if given the account id of the currently executed smart contract.
///
/// # Errors
///
/// - If `account` does not exist.
/// - If the underlying `account` type does not match.
pub fn get_account_balance<T>(account_id: T::AccountId) -> Result<T::Balance>
where
    T: Environment<Balance = u128>, // Just temporary for the MVP!
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .get_balance(scale::Encode::encode(&account_id))
            .map_err(Into::into)
    })
}

/// Registers a new chain extension.
pub fn register_chain_extension<E>(extension: E)
where
    E: ink_engine::ChainExtension + 'static,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .chain_extension_handler
            .register(Box::new(extension));
    })
}

/// Returns the contents of the past performed environmental debug messages in order.
pub fn recorded_debug_messages() -> RecordedDebugMessages {
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.get_emitted_debug_messages()
    })
}

/// Set to true to disable clearing storage
///
/// # Note
///
/// Useful for benchmarks because it ensures the initialized storage is maintained across
/// runs, because lazy storage structures automatically clear their associated cells when
/// they are dropped.
pub fn set_clear_storage_disabled(_disable: bool) {
    unimplemented!(
        "off-chain environment does not yet support `set_clear_storage_disabled`"
    );
}

/// Advances the chain by a single block.
pub fn advance_block<T>()
where
    T: Environment,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.advance_block();
    })
}

/// Sets a caller for the next call.
pub fn set_caller<T>(caller: T::AccountId)
where
    T: Environment,
    <T as Environment>::AccountId: From<[u8; 32]>,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.set_caller(scale::Encode::encode(&caller));
    })
}

/// Sets the callee for the next call.
pub fn set_callee<T>(callee: T::AccountId)
where
    T: Environment,
    <T as Environment>::AccountId: From<[u8; 32]>,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.set_callee(scale::Encode::encode(&callee));
    })
}

/// Sets an account as a contract
pub fn set_contract<T>(contract: T::AccountId)
where
    T: Environment,
    <T as Environment>::AccountId: From<[u8; 32]>,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .set_contract(scale::Encode::encode(&contract));
    })
}

/// Returns a boolean to indicate whether an account is a contract
pub fn is_contract<T>(contract: T::AccountId) -> bool
where
    T: Environment,
    <T as Environment>::AccountId: From<[u8; 32]>,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .is_contract(scale::Encode::encode(&contract))
    })
}

/// Gets the currently set callee.
///
/// This is account id of the currently executing contract.
pub fn callee<T>() -> T::AccountId
where
    T: Environment,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        let callee = instance.engine.get_callee();
        scale::Decode::decode(&mut &callee[..])
            .unwrap_or_else(|err| panic!("encoding failed: {err}"))
    })
}

/// Returns the total number of reads and writes of the contract's storage.
pub fn get_contract_storage_rw<T>(account_id: &T::AccountId) -> (usize, usize)
where
    T: Environment,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .get_contract_storage_rw(scale::Encode::encode(&account_id))
    })
}

/// Sets the value transferred from the caller to the callee as part of the call.
///
/// Please note that the acting accounts should be set with [`set_caller()`] and
/// [`set_callee()`] beforehand.
pub fn set_value_transferred<T>(value: T::Balance)
where
    T: Environment<Balance = u128>, // Just temporary for the MVP!
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.set_value_transferred(value);
    })
}

/// Transfers value from the caller account to the contract.
///
/// Please note that the acting accounts should be set with [`set_caller()`] and
/// [`set_callee()`] beforehand.
pub fn transfer_in<T>(value: T::Balance)
where
    T: Environment<Balance = u128>, // Just temporary for the MVP!
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        let caller = instance
            .engine
            .exec_context
            .caller
            .as_ref()
            .expect("no caller has been set")
            .as_bytes()
            .to_vec();

        let caller_old_balance = instance
            .engine
            .get_balance(caller.clone())
            .unwrap_or_default();

        let callee = instance.engine.get_callee();
        let contract_old_balance = instance
            .engine
            .get_balance(callee.clone())
            .unwrap_or_default();

        instance
            .engine
            .set_balance(caller, caller_old_balance - value);
        instance
            .engine
            .set_balance(callee, contract_old_balance + value);
        instance.engine.set_value_transferred(value);
    });
}

/// Returns the amount of storage cells used by the account `account_id`.
///
/// Returns `None` if the `account_id` is non-existent.
pub fn count_used_storage_cells<T>(account_id: &T::AccountId) -> Result<usize>
where
    T: Environment,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .count_used_storage_cells(&scale::Encode::encode(&account_id))
            .map_err(Into::into)
    })
}

/// Sets the block timestamp for the next [`advance_block`] invocation.
pub fn set_block_timestamp<T>(value: T::Timestamp)
where
    T: Environment<Timestamp = u64>,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.set_block_timestamp(value);
    })
}

/// Sets the block number for the next [`advance_block`] invocation.
pub fn set_block_number<T>(value: T::BlockNumber)
where
    T: Environment<BlockNumber = u32>,
{
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.set_block_number(value);
    })
}

/// Runs the given closure test function with the default configuration
/// for the off-chain environment.
pub fn run_test<T, F>(f: F) -> Result<()>
where
    T: Environment,
    F: FnOnce(DefaultAccounts<T>) -> Result<()>,
    <T as Environment>::AccountId: From<[u8; 32]>,
{
    let default_accounts = default_accounts::<T>();
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance.engine.initialize_or_reset();

        let encoded_alice = scale::Encode::encode(&default_accounts.alice);
        instance.engine.set_caller(encoded_alice.clone());
        instance.engine.set_callee(encoded_alice.clone());

        // set up the funds for the default accounts
        let substantial = 1_000_000;
        let some = 1_000;
        instance.engine.set_balance(encoded_alice, substantial);
        instance
            .engine
            .set_balance(scale::Encode::encode(&default_accounts.bob), some);
        instance
            .engine
            .set_balance(scale::Encode::encode(&default_accounts.charlie), some);
        instance
            .engine
            .set_balance(scale::Encode::encode(&default_accounts.django), 0);
        instance
            .engine
            .set_balance(scale::Encode::encode(&default_accounts.eve), 0);
        instance
            .engine
            .set_balance(scale::Encode::encode(&default_accounts.frank), 0);
    });
    f(default_accounts)
}

/// Returns the default accounts for testing purposes:
/// Alice, Bob, Charlie, Django, Eve and Frank.
pub fn default_accounts<T>() -> DefaultAccounts<T>
where
    T: Environment,
    <T as Environment>::AccountId: From<[u8; 32]>,
{
    DefaultAccounts {
        alice: T::AccountId::from([0x01; 32]),
        bob: T::AccountId::from([0x02; 32]),
        charlie: T::AccountId::from([0x03; 32]),
        django: T::AccountId::from([0x04; 32]),
        eve: T::AccountId::from([0x05; 32]),
        frank: T::AccountId::from([0x06; 32]),
    }
}

/// The default accounts.
pub struct DefaultAccounts<T>
where
    T: Environment,
{
    /// The predefined `ALICE` account holding substantial amounts of value.
    pub alice: T::AccountId,
    /// The predefined `BOB` account holding some amounts of value.
    pub bob: T::AccountId,
    /// The predefined `CHARLIE` account holding some amounts of value.
    pub charlie: T::AccountId,
    /// The predefined `DJANGO` account holding no value.
    pub django: T::AccountId,
    /// The predefined `EVE` account holding no value.
    pub eve: T::AccountId,
    /// The predefined `FRANK` account holding no value.
    pub frank: T::AccountId,
}

/// Returns the recorded emitted events in order.
pub fn recorded_events() -> impl Iterator<Item = EmittedEvent> {
    <EnvInstance as OnInstance>::on_instance(|instance| {
        instance
            .engine
            .get_emitted_events()
            .map(|evt: ink_engine::test_api::EmittedEvent| evt.into())
    })
}

/// Tests if a contract terminates successfully after `self.env().terminate()`
/// has been called.
///
/// The arguments denote:
///
/// * `should_terminate`: A closure in which the function supposed to terminate is called.
/// * `expected_beneficiary`: The beneficiary account who should have received the
///   remaining value in the contract
/// * `expected_value_transferred_to_beneficiary`: The value which should have been
///   transferred to the `expected_beneficiary`.
/// # Usage
///
/// ```no_compile
/// let should_terminate = move || your_contract.fn_which_should_terminate();
/// ink_env::test::assert_contract_termination::<ink_env::DefaultEnvironment, _>(
///     should_terminate,
///     expected_beneficiary,
///     expected_value_transferred_to_beneficiary
/// );
/// ```
///
/// See `integration-tests/contract-terminate` for a complete usage example.
pub fn assert_contract_termination<T, F>(
    should_terminate: F,
    expected_beneficiary: T::AccountId,
    expected_value_transferred_to_beneficiary: T::Balance,
) where
    T: Environment,
    F: FnMut() + UnwindSafe,
    <T as Environment>::AccountId: Debug,
    <T as Environment>::Balance: Debug,
{
    let value_any = ::std::panic::catch_unwind(should_terminate)
        .expect_err("contract did not terminate");
    let encoded_input = value_any
        .downcast_ref::<Vec<u8>>()
        .expect("panic object can not be cast");
    let (value_transferred, encoded_beneficiary): (T::Balance, Vec<u8>) =
        scale::Decode::decode(&mut &encoded_input[..])
            .unwrap_or_else(|err| panic!("input can not be decoded: {err}"));
    let beneficiary =
        <T::AccountId as scale::Decode>::decode(&mut &encoded_beneficiary[..])
            .unwrap_or_else(|err| panic!("input can not be decoded: {err}"));
    assert_eq!(value_transferred, expected_value_transferred_to_beneficiary);
    assert_eq!(beneficiary, expected_beneficiary);
}

/// Prepend contract message call with value transfer. Used for tests in off-chain
/// environment.
#[macro_export]
macro_rules! pay_with_call {
    ($contract:ident . $message:ident ( $( $params:expr ),* ) , $amount:expr) => {{
        $crate::test::transfer_in::<Environment>($amount);
        $contract.$message($ ($params) ,*)
    }}
}

// from engine/mod.rs
pub trait OnInstance: EnvBackend + TypedEnvBackend {
    fn on_instance<F, R>(f: F) -> R
    where
        F: FnOnce(&mut Self) -> R;
}

// We only use this function when 1) compiling to Wasm 2) compiling for tests.
#[cfg_attr(all(feature = "std", not(test)), allow(dead_code))]
pub(crate) fn decode_instantiate_result<I, E, ContractRef, R>(
    instantiate_result: EnvResult<()>,
    out_address: &mut I,
    out_return_value: &mut I,
) -> EnvResult<ConstructorResult<<R as ConstructorReturnType<ContractRef>>::Output>>
where
    I: scale::Input,
    E: crate::Environment,
    ContractRef: FromAccountId<E>,
    R: ConstructorReturnType<ContractRef>,
{
    match instantiate_result {
        Ok(()) => {
            let account_id = scale::Decode::decode(out_address)?;
            let contract_ref =
                <ContractRef as FromAccountId<E>>::from_account_id(account_id);
            let output = <R as ConstructorReturnType<ContractRef>>::ok(contract_ref);
            Ok(Ok(output))
        }
        Err(EnvError::CalleeReverted) => {
            decode_instantiate_err::<I, E, ContractRef, R>(out_return_value)
        }
        Err(actual_error) => Err(actual_error),
    }
}

#[cfg_attr(all(feature = "std", not(test)), allow(dead_code))]
fn decode_instantiate_err<I, E, ContractRef, R>(
    out_return_value: &mut I,
) -> EnvResult<ConstructorResult<<R as ConstructorReturnType<ContractRef>>::Output>>
where
    I: scale::Input,
    E: crate::Environment,
    ContractRef: FromAccountId<E>,
    R: ConstructorReturnType<ContractRef>,
{
    let constructor_result_variant = out_return_value.read_byte()?;
    match constructor_result_variant {
        // 0 == `ConstructorResult::Ok` variant
        0 => {
            if <R as ConstructorReturnType<ContractRef>>::IS_RESULT {
                let result_variant = out_return_value.read_byte()?;
                match result_variant {
                    // 0 == `Ok` variant
                    0 => panic!("The callee reverted, but did not encode an error in the output buffer."),
                    // 1 == `Err` variant
                    1 => {
                        let contract_err = <<R as ConstructorReturnType<ContractRef>>::Error
                        as scale::Decode>::decode(out_return_value)?;
                        let err = <R as ConstructorReturnType<ContractRef>>::err(contract_err)
                            .unwrap_or_else(|| {
                                panic!("Expected an error instance for return type where IS_RESULT == true")
                            });
                        Ok(Ok(err))
                    }
                    _ => Err(Error::Decode(
                        "Invalid inner constructor Result encoding, expected 0 or 1 as the first byte".into())
                    )
                }
            } else {
                panic!("The callee reverted, but did not encode an error in the output buffer.")
            }
        }
        // 1 == `ConstructorResult::Err` variant
        1 => {
            let lang_err = <LangError as scale::Decode>::decode(out_return_value)?;
            Ok(Err(lang_err))
        }
        _ => Err(Error::Decode(
            "Invalid outer constructor Result encoding, expected 0 or 1 as the first byte".into())
        )
    }
}

#[cfg(test)]
mod decode_instantiate_result_tests {
    use super::*;
    use crate::{
        DefaultEnvironment,
        Environment,
        Error,
    };
    use scale::Encode;

    // The `Result` type used to represent the programmer defined contract output.
    type ContractResult<T, E> = Result<T, E>;

    #[derive(scale::Encode, scale::Decode)]
    struct ContractError(String);

    type AccountId = <DefaultEnvironment as Environment>::AccountId;
    struct TestContractRef(AccountId);

    impl crate::ContractEnv for TestContractRef {
        type Env = DefaultEnvironment;
    }

    impl FromAccountId<DefaultEnvironment> for TestContractRef {
        fn from_account_id(account_id: AccountId) -> Self {
            Self(account_id)
        }
    }

    fn encode_and_decode_return_value(
        return_value: ConstructorResult<Result<(), ContractError>>,
    ) -> EnvResult<ConstructorResult<Result<TestContractRef, ContractError>>> {
        let out_address = Vec::new();
        let encoded_return_value = return_value.encode();
        decode_return_value_fallible(
            &mut &out_address[..],
            &mut &encoded_return_value[..],
        )
    }

    fn decode_return_value_fallible<I: scale::Input>(
        out_address: &mut I,
        out_return_value: &mut I,
    ) -> EnvResult<ConstructorResult<Result<TestContractRef, ContractError>>> {
        decode_instantiate_result::<
            I,
            DefaultEnvironment,
            TestContractRef,
            Result<TestContractRef, ContractError>,
        >(Err(Error::CalleeReverted), out_address, out_return_value)
    }

    #[test]
    #[should_panic(
        expected = "The callee reverted, but did not encode an error in the output buffer."
    )]
    fn revert_branch_rejects_valid_output_buffer_with_success_case() {
        let return_value = ConstructorResult::Ok(ContractResult::Ok(()));

        let _decoded_result = encode_and_decode_return_value(return_value);
    }

    #[test]
    fn succesful_dispatch_with_error_from_contract_constructor() {
        let return_value = ConstructorResult::Ok(ContractResult::Err(ContractError(
            "Contract's constructor failed.".to_owned(),
        )));

        let decoded_result = encode_and_decode_return_value(return_value);

        assert!(matches!(
            decoded_result,
            EnvResult::Ok(ConstructorResult::Ok(ContractResult::Err(ContractError(_))))
        ))
    }

    #[test]
    fn dispatch_error_gets_decoded_correctly() {
        let return_value =
            ConstructorResult::Err(ink_primitives::LangError::CouldNotReadInput);

        let decoded_result = encode_and_decode_return_value(return_value);

        assert!(matches!(
            decoded_result,
            EnvResult::Ok(ConstructorResult::Err(
                ink_primitives::LangError::CouldNotReadInput
            ))
        ))
    }

    #[test]
    fn invalid_bytes_in_output_buffer_fail_decoding() {
        let out_address = Vec::new();
        let invalid_encoded_return_value = vec![69];

        let decoded_result = decode_return_value_fallible(
            &mut &out_address[..],
            &mut &invalid_encoded_return_value[..],
        );

        assert!(matches!(decoded_result, Err(crate::Error::Decode(_))))
    }
}

// from call/call_builder.rs
/// The final parameters to the cross-contract call.
#[derive(Debug)]
pub struct CallParams<E, CallType, Args, R>
where
    E: Environment,
{
    /// A marker to indicate which type of call to perform.
    call_type: CallType,
    /// The flags used to change the behavior of a contract call.
    call_flags: CallFlags,
    /// The expected return type.
    _return_type: ReturnType<R>,
    /// The inputs to the execution which is a selector and encoded arguments.
    exec_input: ExecutionInput<Args>,
    /// `Environment` is used by `CallType` for correct types
    _phantom: PhantomData<fn() -> E>,
}

impl<E, CallType, Args, R> CallParams<E, CallType, Args, R>
where
    E: Environment,
{
    /// Returns the call flags.
    #[inline]
    pub fn call_flags(&self) -> &CallFlags {
        &self.call_flags
    }

    /// Returns the execution input.
    #[inline]
    pub fn exec_input(&self) -> &ExecutionInput<Args> {
        &self.exec_input
    }
}

impl<E, Args, R> CallParams<E, Call<E>, Args, R>
where
    E: Environment,
{
    /// Returns the account ID of the called contract instance.
    #[inline]
    pub fn callee(&self) -> &E::AccountId {
        &self.call_type.callee
    }

    /// Returns the chosen gas limit for the called contract execution.
    #[inline]
    pub fn gas_limit(&self) -> Gas {
        self.call_type.gas_limit
    }

    /// Returns the transferred value for the called contract.
    #[inline]
    pub fn transferred_value(&self) -> &E::Balance {
        &self.call_type.transferred_value
    }
}

impl<E, Args, R> CallParams<E, DelegateCall<E>, Args, R>
where
    E: Environment,
{
    /// Returns the code hash which we use to perform a delegate call.
    #[inline]
    pub fn code_hash(&self) -> &E::Hash {
        &self.call_type.code_hash
    }
}

impl<E, Args, R> CallParams<E, Call<E>, Args, R>
where
    E: Environment,
    Args: scale::Encode,
    R: scale::Decode,
{
    /// Invokes the contract with the given built-up call parameters.
    ///
    /// Returns the result of the contract execution.
    ///
    /// # Panics
    ///
    /// This method panics if it encounters an [`ink::env::Error`][`crate::Error`] or an
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`]. If you want to handle
    /// those use the [`try_invoke`][`CallParams::try_invoke`] method instead.
    pub fn invoke(&self) -> R {
        crate::invoke_contract(self)
            .unwrap_or_else(|env_error| {
                panic!("Cross-contract call failed with {env_error:?}")
            })
            .unwrap_or_else(|lang_error| {
                panic!("Cross-contract call failed with {lang_error:?}")
            })
    }

    /// Invokes the contract with the given built-up call parameters.
    ///
    /// Returns the result of the contract execution.
    ///
    /// # Note
    ///
    /// On failure this returns an outer [`ink::env::Error`][`crate::Error`] or inner
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`], both of which can be
    /// handled by the caller.
    pub fn try_invoke(
        &self,
    ) -> core::result::Result<ink_primitives::MessageResult<R>, crate::Error> {
        crate::invoke_contract(self)
    }
}

impl<E, Args, R> CallParams<E, DelegateCall<E>, Args, R>
where
    E: Environment,
    Args: scale::Encode,
    R: scale::Decode,
{
    /// Invoke the contract using Delegate Call semantics with the given built-up call
    /// parameters.
    ///
    /// Returns the result of the contract execution.
    ///
    /// # Panics
    ///
    /// This method panics if it encounters an [`ink::env::Error`][`crate::Error`] or an
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`]. If you want to handle
    /// those use the [`try_invoke`][`CallParams::try_invoke`] method instead.
    pub fn invoke(&self) -> R {
        crate::invoke_contract_delegate(self)
            .unwrap_or_else(|env_error| {
                panic!("Cross-contract call failed with {env_error:?}")
            })
            .unwrap_or_else(|lang_error| {
                panic!("Cross-contract call failed with {lang_error:?}")
            })
    }

    /// Invoke the contract using Delegate Call semantics with the given built-up call
    /// parameters.
    ///
    /// Returns the result of the contract execution.
    ///
    /// # Note
    ///
    /// On failure this returns an outer [`ink::env::Error`][`crate::Error`] or inner
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`], both of which can be
    /// handled by the caller.
    pub fn try_invoke(
        &self,
    ) -> core::result::Result<ink_primitives::MessageResult<R>, crate::Error> {
        crate::invoke_contract_delegate(self)
    }
}

/// Returns a new [`CallBuilder`] to build up the parameters to a cross-contract call.
///
/// # Example
///
/// **Note:** The shown examples panic because there is currently no cross-calling
///           support in the off-chain testing environment. However, this code
///           should work fine in on-chain environments.
///
/// ## Example 1: No Return Value
///
/// The below example shows calling of a message of another contract that does
/// not return any value back to its caller. The called function:
///
/// - has a selector equal to `0xDEADBEEF`
/// - is provided with 5000 units of gas for its execution
/// - is provided with 10 units of transferred value for the contract instance
/// - receives the following arguments in order 1. an `i32` with value `42` 2. a `bool`
///   with value `true` 3. an array of 32 `u8` with value `0x10`
///
/// ```should_panic
/// # use ::ink_env::{
/// #     Environment,
/// #     DefaultEnvironment,
/// #     call::{build_call, Selector, ExecutionInput}
/// # };
/// # use ink_env::call::Call;
/// # type AccountId = <DefaultEnvironment as Environment>::AccountId;
/// # type Balance = <DefaultEnvironment as Environment>::Balance;
/// build_call::<DefaultEnvironment>()
///     .call(AccountId::from([0x42; 32]))
///     .gas_limit(5000)
///     .transferred_value(10)
///     .exec_input(
///         ExecutionInput::new(Selector::new([0xDE, 0xAD, 0xBE, 0xEF]))
///             .push_arg(42u8)
///             .push_arg(true)
///             .push_arg(&[0x10u8; 32]),
///     )
///     .returns::<()>()
///     .invoke();
/// ```
///
/// ## Example 2: With Return Value
///
/// The below example shows calling of a message of another contract that does
/// return a `i32` value back to its caller. The called function:
///
/// - has a selector equal to `0xDEADBEEF`
/// - is provided with 5000 units of gas for its execution
/// - is provided with 10 units of transferred value for the contract instance
/// - receives the following arguments in order 1. an `i32` with value `42` 2. a `bool`
///   with value `true` 3. an array of 32 `u8` with value `0x10`
///
/// ```should_panic
/// # use ::ink_env::{
/// #     Environment,
/// #     DefaultEnvironment,
/// #     call::{build_call, Selector, ExecutionInput, Call},
/// # };
/// # type AccountId = <DefaultEnvironment as Environment>::AccountId;
/// let my_return_value: i32 = build_call::<DefaultEnvironment>()
///     .call_type(Call::new(AccountId::from([0x42; 32])))
///     .gas_limit(5000)
///     .transferred_value(10)
///     .exec_input(
///         ExecutionInput::new(Selector::new([0xDE, 0xAD, 0xBE, 0xEF]))
///             .push_arg(42u8)
///             .push_arg(true)
///             .push_arg(&[0x10u8; 32]),
///     )
///     .returns::<i32>()
///     .invoke();
/// ```
///
/// ## Example 3: Delegate call
///
/// **Note:** The shown example panics because there is currently no delegate calling
///           support in the off-chain testing environment. However, this code
///           should work fine in on-chain environments.
///
/// ```should_panic
/// # use ::ink_env::{
/// #     Environment,
/// #     DefaultEnvironment,
/// #     call::{build_call, Selector, ExecutionInput, utils::ReturnType, DelegateCall},
/// # };
/// # use ink_primitives::Clear;
/// # type AccountId = <DefaultEnvironment as Environment>::AccountId;
/// let my_return_value: i32 = build_call::<DefaultEnvironment>()
///     .delegate(<DefaultEnvironment as Environment>::Hash::CLEAR_HASH)
///     .exec_input(
///         ExecutionInput::new(Selector::new([0xDE, 0xAD, 0xBE, 0xEF]))
///             .push_arg(42u8)
///             .push_arg(true)
///             .push_arg(&[0x10u8; 32])
///     )
///     .returns::<i32>()
///     .invoke();
/// ```
///
/// # Handling `LangError`s
///
/// It is also important to note that there are certain types of errors which can happen
/// during cross-contract calls which can be handled know as
/// [`LangError`][`ink_primitives::LangError`].
///
/// If you want to handle these errors use the [`CallBuilder::try_invoke`] methods instead
/// of the [`CallBuilder::invoke`] ones.
///
/// **Note:** The shown examples panic because there is currently no cross-calling
///           support in the off-chain testing environment. However, this code
///           should work fine in on-chain environments.
///
/// ## Example: Handling a `LangError`
///
/// ```should_panic
/// # use ::ink_env::{
/// #     Environment,
/// #     DefaultEnvironment,
/// #     call::{build_call, Selector, ExecutionInput}
/// # };
/// # use ink_env::call::Call;
/// # type AccountId = <DefaultEnvironment as Environment>::AccountId;
/// # type Balance = <DefaultEnvironment as Environment>::Balance;
/// let call_result = build_call::<DefaultEnvironment>()
///     .call(AccountId::from([0x42; 32]))
///     .gas_limit(5000)
///     .transferred_value(10)
///     .try_invoke()
///     .expect("Got an error from the Contract's pallet.");
///
/// match call_result {
///     Ok(_) => unimplemented!(),
///     Err(e @ ink_primitives::LangError::CouldNotReadInput) => unimplemented!(),
///     Err(_) => unimplemented!(),
/// }
/// ```
#[allow(clippy::type_complexity)]
pub fn build_call<E>() -> CallBuilder<
    E,
    Unset<Call<E>>,
    Unset<ExecutionInput<EmptyArgumentList>>,
    Unset<ReturnType<()>>,
>
where
    E: Environment,
{
    CallBuilder {
        call_type: Default::default(),
        call_flags: Default::default(),
        exec_input: Default::default(),
        return_type: Default::default(),
        _phantom: Default::default(),
    }
}

/// The default call type for cross-contract calls. Performs a cross-contract call to
/// `callee` with gas limit `gas_limit`, transferring `transferred_value` of currency.
#[derive(Clone)]
pub struct Call<E: Environment> {
    callee: E::AccountId,
    gas_limit: Gas,
    transferred_value: E::Balance,
}

impl<E: Environment> Call<E> {
    /// Returns a clean builder for [`Call`].
    pub fn new(callee: E::AccountId) -> Self {
        Self {
            callee,
            gas_limit: Default::default(),
            transferred_value: E::Balance::zero(),
        }
    }
}

impl<E> Call<E>
where
    E: Environment,
{
    /// Sets the `gas_limit` for the current cross-contract call.
    pub fn gas_limit(self, gas_limit: Gas) -> Self {
        Call {
            callee: self.callee,
            gas_limit,
            transferred_value: self.transferred_value,
        }
    }

    /// Sets the `transferred_value` for the current cross-contract call.
    pub fn transferred_value(self, transferred_value: E::Balance) -> Self {
        Call {
            callee: self.callee,
            gas_limit: self.gas_limit,
            transferred_value,
        }
    }
}

/// The `delegatecall` call type. Performs a call with the given code hash.
pub struct DelegateCall<E: Environment> {
    code_hash: E::Hash,
}

impl<E: Environment> DelegateCall<E> {
    /// Returns a clean builder for [`DelegateCall`]
    pub const fn new(code_hash: E::Hash) -> Self {
        DelegateCall { code_hash }
    }
}

impl<E: Environment> DelegateCall<E> {
    /// Sets the `code_hash` to perform a delegate call with.
    pub fn code_hash(self, code_hash: E::Hash) -> Self {
        DelegateCall { code_hash }
    }
}

/// Builds up a cross contract call.
#[derive(Clone)]
pub struct CallBuilder<E, CallType, Args, RetType>
where
    E: Environment,
{
    /// The current parameters that have been built up so far.
    call_type: CallType,
    call_flags: CallFlags,
    exec_input: Args,
    return_type: RetType,
    _phantom: PhantomData<fn() -> E>,
}

impl<E, CallType, Args, RetType> CallBuilder<E, Unset<CallType>, Args, RetType>
where
    E: Environment,
{
    /// The type of the call.
    #[inline]
    #[must_use]
    pub fn call_type<NewCallType>(
        self,
        call_type: NewCallType,
    ) -> CallBuilder<E, Set<NewCallType>, Args, RetType> {
        CallBuilder {
            call_type: Set(call_type),
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }
}

impl<E, CallType, Args, RetType> CallBuilder<E, CallType, Args, RetType>
where
    E: Environment,
{
    /// The flags used to change the behavior of the contract call.
    #[inline]
    #[must_use]
    pub fn call_flags(
        self,
        call_flags: CallFlags,
    ) -> CallBuilder<E, CallType, Args, RetType> {
        CallBuilder {
            call_type: self.call_type,
            call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }
}

impl<E, CallType, Args> CallBuilder<E, CallType, Args, Unset<ReturnType<()>>>
where
    E: Environment,
{
    /// Sets the type of the returned value upon the execution of the call.
    ///
    /// # Note
    ///
    /// Either use `.returns::<()>` to signal that the call does not return a value
    /// or use `.returns::<T>` to signal that the call returns a value of type `T`.
    #[inline]
    pub fn returns<R>(self) -> CallBuilder<E, CallType, Args, Set<ReturnType<R>>> {
        CallBuilder {
            call_type: self.call_type,
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: Set(Default::default()),
            _phantom: Default::default(),
        }
    }
}

impl<E, CallType, RetType>
    CallBuilder<E, CallType, Unset<ExecutionInput<EmptyArgumentList>>, RetType>
where
    E: Environment,
{
    /// Sets the execution input to the given value.
    pub fn exec_input<Args>(
        self,
        exec_input: ExecutionInput<Args>,
    ) -> CallBuilder<E, CallType, Set<ExecutionInput<Args>>, RetType> {
        CallBuilder {
            call_type: self.call_type,
            call_flags: self.call_flags,
            exec_input: Set(exec_input),
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }
}

impl<E, CallType, Args, RetType> CallBuilder<E, Unset<CallType>, Args, RetType>
where
    E: Environment,
{
    /// Prepares the `CallBuilder` for a cross-contract [`Call`].
    pub fn call(
        self,
        callee: E::AccountId,
    ) -> CallBuilder<E, Set<Call<E>>, Args, RetType> {
        CallBuilder {
            call_type: Set(Call::new(callee)),
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }

    /// Prepares the `CallBuilder` for a cross-contract [`DelegateCall`].
    pub fn delegate(
        self,
        code_hash: E::Hash,
    ) -> CallBuilder<E, Set<DelegateCall<E>>, Args, RetType> {
        CallBuilder {
            call_type: Set(DelegateCall::new(code_hash)),
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }
}

impl<E, Args, RetType> CallBuilder<E, Set<Call<E>>, Args, RetType>
where
    E: Environment,
{
    /// Sets the `gas_limit` for the current cross-contract call.
    pub fn gas_limit(self, gas_limit: Gas) -> Self {
        let call_type = self.call_type.value();
        CallBuilder {
            call_type: Set(Call {
                callee: call_type.callee,
                gas_limit,
                transferred_value: call_type.transferred_value,
            }),
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }

    /// Sets the `transferred_value` for the current cross-contract call.
    pub fn transferred_value(self, transferred_value: E::Balance) -> Self {
        let call_type = self.call_type.value();
        CallBuilder {
            call_type: Set(Call {
                callee: call_type.callee,
                gas_limit: call_type.gas_limit,
                transferred_value,
            }),
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }
}

impl<E, Args, RetType> CallBuilder<E, Set<DelegateCall<E>>, Args, RetType>
where
    E: Environment,
{
    /// Sets the `code_hash` to perform a delegate call with.
    pub fn code_hash(self, code_hash: E::Hash) -> Self {
        CallBuilder {
            call_type: Set(DelegateCall { code_hash }),
            call_flags: self.call_flags,
            exec_input: self.exec_input,
            return_type: self.return_type,
            _phantom: Default::default(),
        }
    }
}

impl<E, Args, RetType>
    CallBuilder<E, Set<Call<E>>, Set<ExecutionInput<Args>>, Set<ReturnType<RetType>>>
where
    E: Environment,
{
    /// Finalizes the call builder to call a function.
    pub fn params(self) -> CallParams<E, Call<E>, Args, RetType> {
        CallParams {
            call_type: self.call_type.value(),
            call_flags: self.call_flags,
            _return_type: Default::default(),
            exec_input: self.exec_input.value(),
            _phantom: self._phantom,
        }
    }
}

impl<E, Args, RetType>
    CallBuilder<
        E,
        Set<DelegateCall<E>>,
        Set<ExecutionInput<Args>>,
        Set<ReturnType<RetType>>,
    >
where
    E: Environment,
{
    /// Finalizes the call builder to call a function.
    pub fn params(self) -> CallParams<E, DelegateCall<E>, Args, RetType> {
        CallParams {
            call_type: self.call_type.value(),
            call_flags: self.call_flags,
            _return_type: Default::default(),
            exec_input: self.exec_input.value(),
            _phantom: self._phantom,
        }
    }
}

impl<E, RetType>
    CallBuilder<E, Set<Call<E>>, Unset<ExecutionInput<EmptyArgumentList>>, Unset<RetType>>
where
    E: Environment,
{
    /// Finalizes the call builder to call a function.
    pub fn params(self) -> CallParams<E, Call<E>, EmptyArgumentList, ()> {
        CallParams {
            call_type: self.call_type.value(),
            call_flags: self.call_flags,
            _return_type: Default::default(),
            exec_input: Default::default(),
            _phantom: self._phantom,
        }
    }
}

impl<E, RetType>
    CallBuilder<
        E,
        Set<DelegateCall<E>>,
        Unset<ExecutionInput<EmptyArgumentList>>,
        Unset<RetType>,
    >
where
    E: Environment,
{
    /// Finalizes the call builder to call a function.
    pub fn params(self) -> CallParams<E, DelegateCall<E>, EmptyArgumentList, ()> {
        CallParams {
            call_type: self.call_type.value(),
            call_flags: self.call_flags,
            _return_type: Default::default(),
            exec_input: Default::default(),
            _phantom: self._phantom,
        }
    }
}

impl<E>
    CallBuilder<
        E,
        Set<Call<E>>,
        Unset<ExecutionInput<EmptyArgumentList>>,
        Unset<ReturnType<()>>,
    >
where
    E: Environment,
{
    /// Invokes the cross-chain function call.
    ///
    /// # Panics
    ///
    /// This method panics if it encounters an [`ink::env::Error`][`crate::Error`] or an
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`]. If you want to handle
    /// those use the [`try_invoke`][`CallBuilder::try_invoke`] method instead.
    pub fn invoke(self) {
        self.params().invoke()
    }

    /// Invokes the cross-chain function call.
    ///
    /// # Note
    ///
    /// On failure this returns an outer [`ink::env::Error`][`crate::Error`] or inner
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`], both of which can be
    /// handled by the caller.
    pub fn try_invoke(self) -> Result<ink_primitives::MessageResult<()>> {
        self.params().try_invoke()
    }
}

impl<E>
    CallBuilder<
        E,
        Set<DelegateCall<E>>,
        Unset<ExecutionInput<EmptyArgumentList>>,
        Unset<ReturnType<()>>,
    >
where
    E: Environment,
{
    /// Invokes the cross-chain function call using Delegate Call semantics.
    ///
    /// # Panics
    ///
    /// This method panics if it encounters an [`ink::env::Error`][`crate::Error`]
    /// If you want to handle those use the [`try_invoke`][`CallBuilder::try_invoke`]
    /// method instead.
    pub fn invoke(self) {
        self.params().invoke()
    }

    /// Invokes the cross-chain function call using Delegate Call semantics.
    ///
    /// # Note
    ///
    /// On failure this an [`ink::env::Error`][`crate::Error`] which can be handled by the
    /// caller.
    pub fn try_invoke(self) -> Result<ink_primitives::MessageResult<()>> {
        self.params().try_invoke()
    }
}

impl<E, Args, R>
    CallBuilder<E, Set<Call<E>>, Set<ExecutionInput<Args>>, Set<ReturnType<R>>>
where
    E: Environment,
    Args: scale::Encode,
    R: scale::Decode,
{
    /// Invokes the cross-chain function call and returns the result.
    ///
    /// # Panics
    ///
    /// This method panics if it encounters an [`ink::env::Error`][`crate::Error`] or an
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`]. If you want to handle
    /// those use the [`try_invoke`][`CallBuilder::try_invoke`] method instead.
    pub fn invoke(self) -> R {
        self.params().invoke()
    }

    /// Invokes the cross-chain function call and returns the result.
    ///
    /// # Note
    ///
    /// On failure this returns an outer [`ink::env::Error`][`crate::Error`] or inner
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`], both of which can be
    /// handled by the caller.
    pub fn try_invoke(self) -> Result<ink_primitives::MessageResult<R>> {
        self.params().try_invoke()
    }
}

impl<E, Args, R>
    CallBuilder<E, Set<DelegateCall<E>>, Set<ExecutionInput<Args>>, Set<ReturnType<R>>>
where
    E: Environment,
    Args: scale::Encode,
    R: scale::Decode,
{
    /// Invokes the cross-chain function call using Delegate Call semantics and returns
    /// the result.
    ///
    /// # Panics
    ///
    /// This method panics if it encounters an [`ink::env::Error`][`crate::Error`] or an
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`]. If you want to handle
    /// those use the [`try_invoke`][`CallBuilder::try_invoke`] method instead.
    pub fn invoke(self) -> R {
        self.params().invoke()
    }

    /// Invokes the cross-chain function call using Delegate Call semantics and returns
    /// the result.
    ///
    /// # Note
    ///
    /// On failure this returns an outer [`ink::env::Error`][`crate::Error`] or inner
    /// [`ink::primitives::LangError`][`ink_primitives::LangError`], both of which can be
    /// handled by the caller.
    pub fn try_invoke(self) -> Result<ink_primitives::MessageResult<R>> {
        self.params().try_invoke()
    }
}

// from backend.rs
/// The flags to indicate further information about the end of a contract execution.
#[derive(Default)]
pub struct ReturnFlags {
    value: u32,
}

impl ReturnFlags {
    /// Initialize [`ReturnFlags`] with the reverted flag.
    pub fn new_with_reverted(has_reverted: bool) -> Self {
        Self::default().set_reverted(has_reverted)
    }

    /// Sets the bit to indicate that the execution is going to be reverted.
    #[must_use]
    pub fn set_reverted(mut self, has_reverted: bool) -> Self {
        match has_reverted {
            true => self.value |= has_reverted as u32,
            false => self.value &= !has_reverted as u32,
        }
        self
    }

    /// Returns the underlying `u32` representation.
    #[cfg(not(feature = "std"))]
    pub(crate) fn into_u32(self) -> u32 {
        self.value
    }
}

/// The flags used to change the behavior of a contract call.
#[must_use]
#[derive(Copy, Clone, Debug, Default)]
pub struct CallFlags {
    forward_input: bool,
    clone_input: bool,
    tail_call: bool,
    allow_reentry: bool,
}

impl CallFlags {
    /// Forwards the input for the current function to the callee.
    ///
    /// # Note
    ///
    /// A forwarding call will consume the current contracts input. Any attempt to
    /// access the input after this call returns (e.g. by trying another forwarding call)
    /// will lead to a contract revert.
    /// Consider using [`Self::set_clone_input`] in order to preserve the input.
    pub const fn set_forward_input(mut self, forward_input: bool) -> Self {
        self.forward_input = forward_input;
        self
    }

    /// Identical to [`Self::set_forward_input`] but without consuming the input.
    ///
    /// This adds some additional weight costs to the call.
    ///
    /// # Note
    ///
    /// This implies [`Self::set_forward_input`] and takes precedence when both are set.
    pub const fn set_clone_input(mut self, clone_input: bool) -> Self {
        self.clone_input = clone_input;
        self
    }

    /// Do not return from the call but rather return the result of the callee to the
    /// callers caller.
    ///
    /// # Note
    ///
    /// This makes the current contract completely transparent to its caller by replacing
    /// this contracts potential output with the callee ones. Any code after the contract
    /// calls has been invoked can be safely considered unreachable.
    pub const fn set_tail_call(mut self, tail_call: bool) -> Self {
        self.tail_call = tail_call;
        self
    }

    /// Allow the callee to reenter into the current contract.
    ///
    /// Without this flag any reentrancy into the current contract that originates from
    /// the callee (or any of its callees) is denied. This includes the first callee:
    /// You cannot call into yourself with this flag set.
    pub const fn set_allow_reentry(mut self, allow_reentry: bool) -> Self {
        self.allow_reentry = allow_reentry;
        self
    }

    /// Returns the underlying `u32` representation of the call flags.
    ///
    /// This value is used to forward the call flag information to the
    /// `contracts` pallet.
    pub(crate) const fn into_u32(self) -> u32 {
        self.forward_input as u32
            | ((self.clone_input as u32) << 1)
            | ((self.tail_call as u32) << 2)
            | ((self.allow_reentry as u32) << 3)
    }

    /// Returns `true` if input forwarding is set.
    ///
    /// # Note
    ///
    /// See [`Self::set_forward_input`] for more information.
    pub const fn forward_input(&self) -> bool {
        self.forward_input
    }

    /// Returns `true` if input cloning is set.
    ///
    /// # Note
    ///
    /// See [`Self::set_clone_input`] for more information.
    pub const fn clone_input(&self) -> bool {
        self.clone_input
    }

    /// Returns `true` if the tail call property is set.
    ///
    /// # Note
    ///
    /// See [`Self::set_tail_call`] for more information.
    pub const fn tail_call(&self) -> bool {
        self.tail_call
    }

    /// Returns `true` if call reentry is allowed.
    ///
    /// # Note
    ///
    /// See [`Self::set_allow_reentry`] for more information.
    pub const fn allow_reentry(&self) -> bool {
        self.allow_reentry
    }
}

/// Environmental contract functionality that does not require `Environment`.
pub trait EnvBackend {
    /// Writes the value to the contract storage under the given storage key.
    ///
    /// Returns the size of the pre-existing value at the specified key if any.
    fn set_contract_storage<K, V>(&mut self, key: &K, value: &V) -> Option<u32>
    where
        K: scale::Encode,
        V: Storable;

    /// Returns the value stored under the given storage key in the contract's storage if
    /// any.
    ///
    /// # Errors
    ///
    /// - If the decoding of the typed value failed
    fn get_contract_storage<K, R>(&mut self, key: &K) -> Result<Option<R>>
    where
        K: scale::Encode,
        R: Storable;

    /// Removes the `value` at `key`, returning the previous `value` at `key` from storage
    /// if any.
    ///
    /// # Errors
    ///
    /// - If the decoding of the typed value failed
    fn take_contract_storage<K, R>(&mut self, key: &K) -> Result<Option<R>>
    where
        K: scale::Encode,
        R: Storable;

    /// Returns the size of a value stored under the given storage key is returned if any.
    fn contains_contract_storage<K>(&mut self, key: &K) -> Option<u32>
    where
        K: scale::Encode;

    /// Clears the contract's storage key entry under the given storage key.
    ///
    /// Returns the size of the previously stored value at the specified key if any.
    fn clear_contract_storage<K>(&mut self, key: &K) -> Option<u32>
    where
        K: scale::Encode;

    /// Returns the execution input to the executed contract and decodes it as `T`.
    ///
    /// # Note
    ///
    /// - The input is the 4-bytes selector followed by the arguments of the called
    ///   function in their SCALE encoded representation.
    /// - No prior interaction with the environment must take place before calling this
    ///   procedure.
    ///
    /// # Usage
    ///
    /// Normally contracts define their own `enum` dispatch types respective
    /// to their exported constructors and messages that implement `scale::Decode`
    /// according to the constructors or messages selectors and their arguments.
    /// These `enum` dispatch types are then given to this procedure as the `T`.
    ///
    /// When using ink! users do not have to construct those enum dispatch types
    /// themselves as they are normally generated by the ink! code generation
    /// automatically.
    ///
    /// # Errors
    ///
    /// If the given `T` cannot be properly decoded from the expected input.
    fn decode_input<T>(&mut self) -> Result<T>
    where
        T: scale::Decode;

    /// Returns the value back to the caller of the executed contract.
    ///
    /// # Note
    ///
    /// Calling this method will end contract execution immediately.
    /// It will return the given return value back to its caller.
    ///
    /// The `flags` parameter can be used to revert the state changes of the
    /// entire execution if necessary.
    fn return_value<R>(&mut self, flags: ReturnFlags, return_value: &R) -> !
    where
        R: scale::Encode;

    /// Emit a custom debug message.
    ///
    /// The message is appended to the debug buffer which is then supplied to the calling
    /// RPC client. This buffer is also printed as a debug message to the node console
    /// if the `debug` log level is enabled for the `runtime::contracts` target.
    ///
    /// If debug message recording is disabled in the contracts pallet, which is always
    /// the case when the code is executing on-chain, then this will have no effect.
    fn debug_message(&mut self, content: &str);

    /// Conducts the crypto hash of the given input and stores the result in `output`.
    fn hash_bytes<H>(&mut self, input: &[u8], output: &mut <H as HashOutput>::Type)
    where
        H: CryptoHash;

    /// Conducts the crypto hash of the given encoded input and stores the result in
    /// `output`.
    fn hash_encoded<H, T>(&mut self, input: &T, output: &mut <H as HashOutput>::Type)
    where
        H: CryptoHash,
        T: scale::Encode;

    /// Recovers the compressed ECDSA public key for given `signature` and `message_hash`,
    /// and stores the result in `output`.
    fn ecdsa_recover(
        &mut self,
        signature: &[u8; 65],
        message_hash: &[u8; 32],
        output: &mut [u8; 33],
    ) -> Result<()>;

    /// Retrieves an Ethereum address from the ECDSA compressed `pubkey`
    /// and stores the result in `output`.
    fn ecdsa_to_eth_address(
        &mut self,
        pubkey: &[u8; 33],
        output: &mut [u8; 20],
    ) -> Result<()>;

    /// Low-level interface to call a chain extension method.
    ///
    /// Returns the output of the chain extension of the specified type.
    ///
    /// # Errors
    ///
    /// - If the chain extension with the given ID does not exist.
    /// - If the inputs had an unexpected encoding.
    /// - If the output could not be properly decoded.
    /// - If some extension specific condition has not been met.
    ///
    /// # Developer Note
    ///
    /// A valid implementation applies the `status_to_result` closure on
    /// the status code returned by the actual call to the chain extension
    /// method.
    /// Only if the closure finds that the given status code indicates a
    /// successful call to the chain extension method is the resulting
    /// output buffer passed to the `decode_to_result` closure, in order to
    /// drive the decoding and error management process from the outside.
    fn call_chain_extension<I, T, E, ErrorCode, F, D>(
        &mut self,
        func_id: u32,
        input: &I,
        status_to_result: F,
        decode_to_result: D,
    ) -> ::core::result::Result<T, E>
    where
        I: scale::Encode,
        T: scale::Decode,
        E: From<ErrorCode>,
        F: FnOnce(u32) -> ::core::result::Result<(), ErrorCode>,
        D: FnOnce(&[u8]) -> ::core::result::Result<T, E>;

    /// Sets a new code hash for the current contract.
    ///
    /// This effectively replaces the code which is executed for this contract address.
    ///
    /// # Errors
    ///
    /// - If the supplied `code_hash` cannot be found on-chain.
    fn set_code_hash(&mut self, code_hash: &[u8]) -> Result<()>;
}

/// Environmental contract functionality.
pub trait TypedEnvBackend: EnvBackend {
    /// Returns the address of the caller of the executed contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`caller`][`crate::caller`]
    fn caller<E: Environment>(&mut self) -> E::AccountId;

    /// Returns the transferred value for the contract execution.
    ///
    /// # Note
    ///
    /// For more details visit: [`transferred_value`][`crate::transferred_value`]
    fn transferred_value<E: Environment>(&mut self) -> E::Balance;

    /// Returns the price for the specified amount of gas.
    ///
    /// # Note
    ///
    /// For more details visit: [`weight_to_fee`][`crate::weight_to_fee`]
    fn weight_to_fee<E: Environment>(&mut self, gas: u64) -> E::Balance;

    /// Returns the amount of gas left for the contract execution.
    ///
    /// # Note
    ///
    /// For more details visit: [`gas_left`][`crate::gas_left`]
    fn gas_left<E: Environment>(&mut self) -> u64;

    /// Returns the timestamp of the current block.
    ///
    /// # Note
    ///
    /// For more details visit: [`block_timestamp`][`crate::block_timestamp`]
    fn block_timestamp<E: Environment>(&mut self) -> E::Timestamp;

    /// Returns the address of the executed contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`account_id`][`crate::account_id`]
    fn account_id<E: Environment>(&mut self) -> E::AccountId;

    /// Returns the balance of the executed contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`balance`][`crate::balance`]
    fn balance<E: Environment>(&mut self) -> E::Balance;

    /// Returns the current block number.
    ///
    /// # Note
    ///
    /// For more details visit: [`block_number`][`crate::block_number`]
    fn block_number<E: Environment>(&mut self) -> E::BlockNumber;

    /// Returns the minimum balance that is required for creating an account
    /// (i.e. the chain's existential deposit).
    ///
    /// # Note
    ///
    /// For more details visit: [`minimum_balance`][`crate::minimum_balance`]
    fn minimum_balance<E: Environment>(&mut self) -> E::Balance;

    /// Emits an event with the given event data.
    ///
    /// # Note
    ///
    /// For more details visit: [`emit_event`][`crate::emit_event`]
    fn emit_event<E, Event>(&mut self, event: Event)
    where
        E: Environment,
        Event: Topics + scale::Encode;

    /// Invokes a contract message and returns its result.
    ///
    /// # Note
    ///
    /// For more details visit: [`invoke_contract`][`crate::invoke_contract`]
    fn invoke_contract<E, Args, R>(
        &mut self,
        call_data: &CallParams<E, Call<E>, Args, R>,
    ) -> Result<ink_primitives::MessageResult<R>>
    where
        E: Environment,
        Args: scale::Encode,
        R: scale::Decode;

    /// Invokes a contract message via delegate call and returns its result.
    ///
    /// # Note
    ///
    /// For more details visit:
    /// [`invoke_contract_delegate`][`crate::invoke_contract_delegate`]
    fn invoke_contract_delegate<E, Args, R>(
        &mut self,
        call_data: &CallParams<E, DelegateCall<E>, Args, R>,
    ) -> Result<ink_primitives::MessageResult<R>>
    where
        E: Environment,
        Args: scale::Encode,
        R: scale::Decode;

    /// Instantiates another contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`instantiate_contract`][`crate::instantiate_contract`]
    fn instantiate_contract<E, ContractRef, Args, Salt, R>(
        &mut self,
        params: &CreateParams<E, ContractRef, Args, Salt, R>,
    ) -> Result<
        ink_primitives::ConstructorResult<
            <R as ConstructorReturnType<ContractRef>>::Output,
        >,
    >
    where
        E: Environment,
        ContractRef: FromAccountId<E>,
        Args: scale::Encode,
        Salt: AsRef<[u8]>,
        R: ConstructorReturnType<ContractRef>;

    /// Terminates a smart contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`terminate_contract`][`crate::terminate_contract`]
    fn terminate_contract<E>(&mut self, beneficiary: E::AccountId) -> !
    where
        E: Environment;

    /// Transfers value from the contract to the destination account ID.
    ///
    /// # Note
    ///
    /// For more details visit: [`transfer`][`crate::transfer`]
    fn transfer<E>(&mut self, destination: E::AccountId, value: E::Balance) -> Result<()>
    where
        E: Environment;

    /// Checks whether a specified account belongs to a contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`is_contract`][`crate::is_contract`]
    #[allow(clippy::wrong_self_convention)]
    fn is_contract<E>(&mut self, account: &E::AccountId) -> bool
    where
        E: Environment;

    /// Checks whether the caller of the current contract is the origin of the whole call
    /// stack.
    ///
    /// # Note
    ///
    /// For more details visit: [`caller_is_origin`][`crate::caller_is_origin`]
    fn caller_is_origin<E>(&mut self) -> bool
    where
        E: Environment;

    /// Retrieves the code hash of the contract at the given `account` id.
    ///
    /// # Note
    ///
    /// For more details visit: [`code_hash`][`crate::code_hash`]
    fn code_hash<E>(&mut self, account: &E::AccountId) -> Result<E::Hash>
    where
        E: Environment;

    /// Retrieves the code hash of the currently executing contract.
    ///
    /// # Note
    ///
    /// For more details visit: [`own_code_hash`][`crate::own_code_hash`]
    fn own_code_hash<E>(&mut self) -> Result<E::Hash>
    where
        E: Environment;

    fn call_runtime<E, Call>(&mut self, call: &Call) -> Result<()>
    where
        E: Environment,
        Call: scale::Encode;
}
