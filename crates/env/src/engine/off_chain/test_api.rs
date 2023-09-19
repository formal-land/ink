// Copyright 2018-2022 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Operations on the off-chain testing environment.

// our modifications
pub use super::call_data::CallData;
pub use ink_engine::ChainExtension;

pub use crate::backend_and_call_builder_and_engine_and_engine_test_api_and_error::{
    EmittedEvent,
    set_account_balance,
    get_account_balance,
    register_chain_extension,
    recorded_debug_messages,
    set_clear_storage_disabled,
    advance_block,
    set_caller,
    set_callee,
    set_contract,
    is_contract,
    callee,
    get_contract_storage_rw,
    set_value_transferred,
    transfer_in,
    count_used_storage_cells,
    set_block_timestamp,
    set_block_number,
    run_test,
    default_accounts,
    DefaultAccounts,
    recorded_events,
    assert_contract_termination,
};
