use std::fmt;
use crate::{PDUError, PDUResult};

#[derive(Debug)]
pub struct HexData<'a>(pub &'a [u8]);
impl<'a> fmt::Display for HexData<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for b in self.0.iter() {
            write!(f, "{:02X}", b)?;
        }
        Ok(())
    }
}
impl<'a> HexData<'a> {
    pub fn decode(data: &str) -> PDUResult<Vec<u8>> {
        data.as_bytes()
            .chunks(2)
            .map(::std::str::from_utf8)
            .map(|x| {
                match x {
                    Ok(x) => u8::from_str_radix(x, 16)
                        .map_err(|_| PDUError::InvalidPdu("invalid hex string")),
                    Err(_) => Err(PDUError::InvalidPdu("invalid hex string"))
                }
            })
            .collect()
    }
}
