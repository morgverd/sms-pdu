use std::fmt::Formatter;
use crate::pdu::MessageEncoding;

pub mod pdu;
pub mod gsm_encoding;
pub mod hex;

#[macro_export]
macro_rules! check_offset {
    ($b:ident, $offset:ident, $reason:expr) => {
        if $b.get($offset).is_none() {
            return Err(PDUError::InvalidPdu(concat!("Offset check failed for: ", $reason)));
        }
    }
}

pub type PDUResult<T> = Result<T, PDUError>;

#[derive(Debug)]
pub enum PDUError {
    InvalidPdu(&'static str),
    UnsupportedEncoding(MessageEncoding, Vec<u8>)
}
impl std::fmt::Display for PDUError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            PDUError::InvalidPdu(msg) => write!(f, "Invalid PDU: {}", msg),
            PDUError::UnsupportedEncoding(encoding, data) => write!(f, "Data of unknown encoding: {:?}: {:?}", encoding, data)
        }
    }
}
