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

// our modifications
pub use crate::backend_and_call_builder_and_engine_and_engine_test_api_and_error::OnInstance;
pub(crate) use crate::backend_and_call_builder_and_engine_and_engine_test_api_and_error::decode_instantiate_result;
use cfg_if::cfg_if;

cfg_if! {
    if #[cfg(not(feature = "std"))] {
        mod on_chain;
        pub use self::on_chain::EnvInstance;
    } else {
        pub mod off_chain;
        pub use self::off_chain::EnvInstance;
    }
}
