// Copyright (c) 2022 Espresso Systems (espressosys.com)
// This file is part of the VeriZexe library.

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version. This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details. You should have received a copy of the GNU General Public License along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Error types related to DPC

use ark_std::{convert::From, format, string::String};
use displaydoc::Display;
use jf_plonk::errors::PlonkError;
use jf_primitives::errors::PrimitivesError;

/// All possible categories of error from DPC scheme
#[derive(Display, Debug)]
pub enum DPCApiError {
    /// SNARK failed: {0}.
    FailedSnark(PlonkError),
    /// Crypto primitives failed: {0}.
    FailedPrimitives(PrimitivesError),
    /// Serialization failed: {0}.
    FailedSerialization(ark_serialize::SerializationError),
    /// Out of range, an overflow or underflow occurs: {0}.
    OverOrUnderFlow(String),
    /// General error: {0}.
    GeneralError(String),
    /// Invalid parameters: {0}.
    InvalidParameters(String),
    /// Failed ReceiverMemo Signature: {0}
    FailedReceiverMemoSignature(PrimitivesError),
    /// Failed Authorization Signature: {0}
    FailedAuthorizationSignature(PrimitivesError),
    /// Failed Authorization Signature: {0}
    FailedTransactionVerification(String),
    /// I/O failure: {0}
    IoError(String),
    /// Invalid parameters: {0}
    InvalidParameter(String),
    /// Failed to deserialize: {0}
    DeserializationError(String),
    /// Incorrect fee collection: {0}
    IncorrectFee(String),
    /// Parameters generation error:{0}
    ParametersGenerationError(String),
    #[rustfmt::skip]
    /// ‼ ️Internal error! Please report to Crypto Team immediately!\nMessage: {0}"
    InternalError(String),
}

impl From<PrimitivesError> for DPCApiError {
    fn from(e: PrimitivesError) -> Self {
        DPCApiError::FailedPrimitives(e)
    }
}

impl From<anyhow::Error> for DPCApiError {
    fn from(e: anyhow::Error) -> Self {
        DPCApiError::GeneralError(format!("{:?}", e))
    }
}

impl From<ark_serialize::SerializationError> for DPCApiError {
    fn from(e: ark_serialize::SerializationError) -> Self {
        DPCApiError::FailedSerialization(e)
    }
}

impl From<PlonkError> for DPCApiError {
    fn from(e: PlonkError) -> Self {
        DPCApiError::FailedSnark(e)
    }
}
