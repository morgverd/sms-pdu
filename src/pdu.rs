//! Utilities for dealing with GSM 03.40 Protocol Data Units (PDUs).
//!
//! See [this Wikipedia article](https://en.wikipedia.org/wiki/GSM_03.40) for more genreal
//! information on the format of PDUs.
//!
//! As of the time of writing, this library's implementation of PDUs can be classed as "passable" -
//! in that it currently supports 2 out of the 6 specified PDU types (SMS-DELIVER and SMS-SUBMIT),
//! and straight up refuses to parse anything else. Luckily, these two are the only ones you really
//! need (and if they aren't, feel free to file an issue!).
use std::fmt;
use std::str::FromStr;
use std::convert::{Infallible, TryFrom};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use crate::gsm_encoding::{GsmMessageData, gsm_decode_string, decode_sms_7bit};
use crate::{check_offset, PDUError, PDUResult};

/// Type of number value - used as part of phone numbers to indicate whether the number is
/// international, alphanumeric, etc.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive, Hash)]
pub enum TypeOfNumber {
    /// Unknown number type ('let the network handle it please').
    Unknown = 0b0_000_0000,
    /// International (i.e. starting with +). This is probably what you want when sending messages.
    International = 0b0_001_0000,
    /// National number - no prefix or suffix added.
    National = 0b0_010_0000,
    /// Special number - you can't send messages with this type.
    Special = 0b0_011_0000,
    /// Alphanumeric number - i.e. this isn't a phone number, it's actually some text that
    /// indicates who the sender is (e.g. when banks/other companies send you SMSes).
    ///
    /// You can't send messages with this type.
    Gsm = 0b0_101_0000,
    /// Short number (not in use).
    Short = 0b0_110_0000,
    /// Reserved (not in use).
    Reserved = 0b0_111_0000
}
/// Numbering plan idnficiation value.
///
/// I think this is mostly vestigial, and you'll want to set this to `IsdnTelephone`.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive, Hash)]
pub enum NumberingPlanIdentification {
    NetworkDetermined = 0b0_000_0000,
    IsdnTelephone = 0b0_000_0001,
    Data = 0b0_000_0011,
    Telex = 0b0_000_0100,
    National = 0b0_000_1000,
    Private = 0b0_000_1001,
    Ermes = 0b0_000_1010
}
/// Address type, comprised of a `TypeOfNumber` and `NumberingPlanIdentification` value.
///
/// It is **highly** recommended that you just use the `Default` value of this `struct`, unless you
/// know what you're doing, and that your phone numbers are in international format (i.e. starting
/// with `+`).
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct AddressType {
    pub type_of_number: TypeOfNumber,
    pub numbering_plan_identification: NumberingPlanIdentification
}
impl Default for AddressType {
    fn default() -> Self {
        AddressType {
            type_of_number: TypeOfNumber::International,
            numbering_plan_identification: NumberingPlanIdentification::IsdnTelephone
        }
    }
}
impl TryFrom<u8> for AddressType {
    type Error = PDUError;
    fn try_from(b: u8) -> PDUResult<Self>  {
        let ton = b & 0b0_111_0000;
        let ton = TypeOfNumber::from_u8(ton)
            .ok_or(PDUError::InvalidPdu("invalid type_of_number"))?;
        let npi = b & 0b0_000_1111;
        let npi = NumberingPlanIdentification::from_u8(npi)
            .ok_or(PDUError::InvalidPdu("invalid numbering_plan_identification"))?;
        Ok(Self {
            type_of_number: ton,
            numbering_plan_identification: npi
        })
    }
}
impl Into<u8> for AddressType {
    fn into(self) -> u8 {
        let mut ret: u8 = 0b1_000_0000;
        ret |= self.type_of_number as u8;
        ret |= self.numbering_plan_identification as u8;
        ret
    }
}
/// A GSM phone number, encoded using their weird half-octet encoding.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PhoneNumber(pub Vec<u8>);
/// Make a phone number from some ordinary bytes.
///
/// Note that **only the least significant 4 bytes** are used in this conversion, due to the way
/// GSM phone numbers work. The top 4 bytes are discarded!
impl<'a> From<&'a [u8]> for PhoneNumber {
    fn from(b: &[u8]) -> Self {
        let mut ret = vec![];
        for b in b.iter() {
            let first = b & 0b0000_1111;
            let second = (b & 0b1111_0000) >> 4;
            ret.push(first);
            if second != 0b0000_1111 {
                ret.push(second);
            }
        }
        PhoneNumber(ret)
    }
}
impl PhoneNumber {
    /// Make a `PhoneNumber` for an alphanumeric GSM sender address.
    pub fn from_gsm(b: &[u8], len: usize) -> Self {
        PhoneNumber(decode_sms_7bit(b, 0, len))
    }
    /// Represent this phone number as normal bytes, instead of their weird as hell encoding.
    pub fn as_bytes(&self) -> Vec<u8> {
        let mut ret = vec![];
        let mut cur = 0b0000_0000;
        for (i, b) in self.0.iter().enumerate() {
            let mut b = *b;
            if i % 2 == 0 {
                cur |= b;
            }
            else {
                b = b << 4;
                cur |= b;
                ret.push(cur);
                cur = 0b0000_0000;
            }
        }
        if self.0.len() % 2 != 0 {
            cur |= 0b1111_0000;
            ret.push(cur);
        }
        ret
    }
}
/// A PDU address (i.e. phone number, and number type). This is what you want to use for
/// representing phone numbers, most likely.
///
/// Use the `FromStr` implementation here to convert regular string phone numbers into weird PDU
/// format. Note that alphanumeric numbers are not supported at this time (only normal phone
/// numbers).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PduAddress {
    pub type_addr: AddressType,
    pub number: PhoneNumber
}
impl fmt::Display for PduAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {

        let prefix = match self.type_addr.type_of_number {
            TypeOfNumber::International => "+",
            _ => ""
        };
        write!(f, "{}", prefix)?;
        if self.type_addr.type_of_number == TypeOfNumber::Gsm {
            write!(f, "{}", gsm_decode_string(&self.number.0))?;
        }
        else {
            for b in self.number.0.iter() {
                write!(f, "{}", b)?;
            }
        }
        Ok(())
    }
}
impl FromStr for PduAddress {
    type Err = Infallible;
    fn from_str(st: &str) -> Result<Self, Infallible> {
        let mut int = false;
        let buf = st.chars()
            .filter_map(|x| {
                match x {
                    '0'..='9' => Some(x as u8 - 48),
                    '+' => {
                        int = true;
                        None
                    },
                    _ => None
                }
            }).collect::<Vec<_>>();
        let ton = if int {
            TypeOfNumber::International
        }
        else {
            TypeOfNumber::Unknown
        };
        Ok(PduAddress {
            type_addr: AddressType {
                type_of_number: ton,
                numbering_plan_identification: NumberingPlanIdentification::IsdnTelephone
            },
            number: PhoneNumber(buf)
        })
    }
}
impl<'a> TryFrom<&'a [u8]> for PduAddress {
    type Error = PDUError;
    fn try_from(b: &[u8]) -> PDUResult<Self> {
        if b.len() < 3 {
            Err(PDUError::InvalidPdu("tried to make a PduAddress from less than 3 bytes"))?
        }
        let len = b[0] as usize;
        let type_addr = AddressType::try_from(b[1])?;
        let number = if type_addr.type_of_number == TypeOfNumber::Gsm {
            let len = (len * 4) / 7;
            PhoneNumber::from_gsm(&b[2..], len)
        }
        else {
            PhoneNumber::from(&b[2..])
        };
        Ok(PduAddress { type_addr, number })
    }
}
impl PduAddress {
    /// Convert this address into bytes, as represented in the actual PDU.
    ///
    /// The `broken_len` flag controls whether to represent the length as the length in bytes of
    /// the whole PduAddress (false), or just the length of the phone number contained within (true).
    ///
    /// In testing, it seems as if it should pretty much always be `true`, which is weird. A future
    /// version of the crate may well just remove the parameter and default to true.
    pub fn as_bytes(&self, broken_len: bool) -> Vec<u8> {
        let mut ret = vec![];
        ret.push(self.type_addr.into());
        ret.extend(self.number.as_bytes());
        let len = if broken_len {
            self.number.0.len()
        } else {
            ret.len()
        };
        ret.insert(0, len as u8);
        ret
    }
}
/// SMS PDU message type.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive)]
pub enum MessageType {
    /// SMS-DELIVER (SC to MT) or SMS-DELIVER-REPORT (MT to SC)
    SmsDeliver = 0b000000_00,
    /// SMS-STATUS-REPORT (SC to MT) or SMS-COMMAND (MT to SC)
    SmsCommand = 0b000000_10,
    /// SMS-SUBMIT-REPORT (SC to MT) or SMS-SUBMIT (MT to SC)
    SmsSubmit = 0b000000_01,
    /// Reserved for future use.
    Reserved = 0b000000_11
}
/// Validity of the VP field.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive)]
pub enum VpFieldValidity {
    /// Invalid.
    Invalid = 0b00,
    /// Valid, in relative format.
    Relative = 0b10,
    /// Valid, in enhanced format.
    Enhanced = 0b01,
    /// Valid, in absolute format.
    Absolute = 0b11,
}
/// The first octet of a SMS-SUBMIT PDU.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct PduFirstOctet {
    /// Message type.
    pub mti: MessageType,
    /// Reject duplicates (?).
    pub rd: bool,
    /// Validity and format of the VP field.
    pub vpf: VpFieldValidity,
    /// Whether to request a status report when the message is sent succesfully.
    pub srr: bool,
    /// Does the user data segment contain a data header?
    pub udhi: bool,
    /// Do replies to this message use the same settings as this message?
    pub rp: bool
}
impl From<u8> for PduFirstOctet {
    fn from(b: u8) -> Self {
        let rd = (b & 0b0000_0100) > 0;
        let srr = (b & 0b0010_0000) > 0;
        let udhi = (b & 0b0100_0000) > 0;
        let rp = (b & 0b1000_0000) > 0;
        let mti = MessageType::from_u8(b & 0b0000_0011)
            .expect("MessageType conversions should be exhaustive!");
        let vpf = VpFieldValidity::from_u8((b & 0b0001_1000) >> 3)
            .expect("VpFieldValidity conversions should be exhaustive!");
        PduFirstOctet { rd, srr, udhi, rp, mti, vpf }
    }
}
impl Into<u8> for PduFirstOctet {
    fn into(self) -> u8 {
        let mut ret = 0b0000_0000;
        ret |= self.mti as u8;
        ret |= (self.vpf as u8) << 3;
        if self.rd {
            ret |= 0b0000_0100;
        }
        if self.srr {
            ret |= 0b0010_0000;
        }
        if self.udhi {
            ret |= 0b0100_0000;
        }
        if self.rp {
            ret |= 0b1000_0000;
        }
        ret
    }
}
/// The data coding scheme of the message.
///
/// Basically, this `enum` is a decoded 8-bit field that has a bunch of different cases, which is
/// why there are so many options here.
///
/// The meanings explained in the Huawei spec are very confusing and sometimes overlapping.
/// Use the `encoding` method to figure out what encoding to use, which is probably the only real
/// use you're going to have for this `struct` anyway.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DataCodingScheme {
    /// Standard coding scheme.
    Standard {
        /// Whether or not the message is compressed, but this isn't actually supported.
        compressed: bool,
        /// The message class (flash SMS, stored to SIM only, etc.)
        class: Option<MessageClass>,
        /// The message encoding (7-bit, UCS-2, 8-bit)
        encoding: MessageEncoding
    },
    /// Reserved value.
    Reserved,
    /// Discard the message content, but display the message waiting indication to the user.
    MessageWaitingDiscard {
        /// Enables or disables message waiting indication.
        waiting: bool,
        /// Type of message waiting.
        type_indication: MessageWaitingType,
    },
    /// Store the message content, and display the message waiting indication to the user.
    MessageWaiting {
        /// Enables or disables message waiting indication.
        waiting: bool,
        /// Type of message waiting.
        type_indication: MessageWaitingType,
        /// Whether or not the message is encoded in UCS-2 format.
        ucs2: bool
    }
}
impl DataCodingScheme {
    /// Determine which character encoding the message uses (i.e. GSM 7-bit, UCS-2, ...)
    ///
    /// (Some of these answers might be guesses.)
    pub fn encoding(&self) -> MessageEncoding {
        use self::DataCodingScheme::*;
        match *self {
            Standard { encoding, .. } => encoding,
            Reserved => MessageEncoding::Gsm7Bit,
            MessageWaitingDiscard { .. } => MessageEncoding::Gsm7Bit,
            MessageWaiting { ucs2, .. } => if ucs2 {
                MessageEncoding::Ucs2
            }
            else {
                MessageEncoding::Gsm7Bit
            }
        }
    }
}
impl From<u8> for DataCodingScheme {
    fn from(b: u8) -> Self {
        if (b & 0b1100_0000) == 0b0000_0000 {
            let compressed = (b & 0b0010_0000) > 0;
            let reserved = (b & 0b0001_0000) > 0;
            let class = Some(if reserved {
                // XXX: No default is actually specified in the Huawei spec; I just chose
                // StoreToNv, because that's what we send by default.
                MessageClass::StoreToNv
            }
            else {
                MessageClass::from_u8(b & 0b0000_0011)
                    .expect("MessageClass conversions should be exhaustive!")
            });
            let encoding = MessageEncoding::from_u8(b & 0b0000_1100)
                .expect("MessageEncoding conversions should be exhaustive!");
            DataCodingScheme::Standard { compressed, class, encoding }
        }
        else if (b & 0b1111_0000) == 0b1111_0000 {
            let compressed = false;
            let class = Some(MessageClass::from_u8(b & 0b0000_0011)
                .expect("MessageClass conversions should be exhaustive!"));
            let encoding = if (b & 0b0000_0100) > 0 {
                MessageEncoding::Gsm7Bit
            }
            else {
                MessageEncoding::EightBit
            };
            DataCodingScheme::Standard { compressed, class, encoding }
        }
        else if (b & 0b1111_0000) == 0b1100_0000 {
            let waiting = (b & 0b0000_1000) > 0;
            let type_indication = MessageWaitingType::from_u8(b & 0b0000_0011)
                .expect("MessageWaitingType conversions should be exhaustive!");
            DataCodingScheme::MessageWaitingDiscard { waiting, type_indication }
        }
        else if (b & 0b1111_0000) == 0b1101_0000 || (b & 0b1111_0000) == 0b1110_0000 {
            let ucs2 = (b & 0b1111_0000) == 0b1110_0000;
            let waiting = (b & 0b0000_1000) > 0;
            let type_indication = MessageWaitingType::from_u8(b & 0b0000_0011)
                .expect("MessageWaitingType conversions should be exhaustive!");
            DataCodingScheme::MessageWaiting { ucs2, waiting, type_indication }
        }
        else {
            DataCodingScheme::Reserved
        }
    }
}
impl Into<u8> for DataCodingScheme {
    fn into(self) -> u8 {
        use self::DataCodingScheme::*;
        match self {
            Standard { compressed, class, encoding } => {
                let mut ret = 0u8;
                if compressed {
                    ret |= 0b0010_0000;
                }
                if let Some(class) = class {
                    ret |= 0b0001_0000;
                    ret |= class as u8;
                }
                ret |= encoding as u8;
                ret
            },
            Reserved => 0b0100_0101,
            MessageWaiting { waiting, type_indication, ucs2 } => {
                let mut ret = if ucs2 {
                    0b1110_0000
                }
                else {
                    0b1101_0000
                };
                if waiting {
                    ret |= 0b0000_1000;
                }
                ret |= type_indication as u8;
                ret
            },
            MessageWaitingDiscard { waiting, type_indication } => {
                let mut ret = 0b1100_0000;
                if waiting {
                    ret |= 0b0000_1000;
                }
                ret |= type_indication as u8;
                ret
            }
        }
    }
}
/// Type of message waiting.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive)]
pub enum MessageWaitingType {
    Voice = 0b000000_00,
    Fax = 0b000000_01,
    Email = 0b000000_10,
    Unknown = 0b000000_11
}
/// Class of message received.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive)]
pub enum MessageClass {
    /// Silent (class 0)  - display on the phone's UI, but don't store in memory.
    Silent = 0b000000_00,
    /// Store to the NV (class 1), or SIM card if the NV is full.
    StoreToNv = 0b000000_01,
    /// Store to the SIM card only (class 2).
    StoreToSim = 0b000000_10,
    /// Store to the TE (class 3).
    StoreToTe = 0b000000_11
}
/// SMS message data encoding.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive)]
pub enum MessageEncoding {
    /// GSM packed 7-bit encoding.
    Gsm7Bit = 0b0000_00_00,
    /// Binary 8-bit encoding.
    EightBit = 0b0000_01_00,
    /// UCS-2 (i.e. UTF-16) encoding.
    Ucs2 = 0b0000_10_00,
    /// Reserved for future use.
    Reserved = 0b0000_11_00,
}
/// The first octet of a SMS-DELIVER PDU.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeliverPduFirstOctet {
    /// Message type.
    mti: MessageType,
    /// Indicates whetehr a status report was requested.
    sri: bool,
    /// Does the user data segment contain a data header?
    udhi: bool,
    /// Do replies to this message use the same settings as this message?
    rp: bool
}
impl From<u8> for DeliverPduFirstOctet {
    fn from(b: u8) -> Self {
        let mti = MessageType::from_u8(b & 0b000000_11)
            .expect("MessageType conversions should be exhaustive!");
        let sri = (b & 0b00100000) > 0;
        let udhi = (b & 0b01000000) > 0;
        let rp = (b & 0b01000000) > 0;
        DeliverPduFirstOctet { mti, sri, udhi, rp }
    }
}
/// Service centre timestamp.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmscTimestamp {
    pub year: u8,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
    /// Hours' difference between local time and GMT.
    pub timezone: u8
}
pub(crate) fn reverse_byte(b: u8) -> u8 {
    let units = b >> 4;
    let tens = b & 0b0000_1111;
    (tens * 10) + units
}
impl<'a> TryFrom<&'a [u8]> for SmscTimestamp {
    type Error = PDUError;
    fn try_from(b: &[u8]) -> PDUResult<Self> {
        if b.len() != 7 {
            Err(PDUError::InvalidPdu("SmscTimestamp must be 7 bytes long"))?
        }
        Ok(SmscTimestamp {
            year: reverse_byte(b[0]),
            month: reverse_byte(b[1]),
            day: reverse_byte(b[2]),
            hour: reverse_byte(b[3]),
            minute: reverse_byte(b[4]),
            second: reverse_byte(b[5]),
            timezone: reverse_byte(b[6]),
        })
    }
}
/// An SMS-DELIVER PDU.
///
/// **NB:** For simple usage, you'll only need to care about the `originating_address` field and
/// the `get_message_data` method!
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeliverPdu {
    /// Service centre address, if provided here.
    pub sca: Option<PduAddress>,
    /// First octet (contains some extra fields).
    pub first_octet: DeliverPduFirstOctet,
    /// Originating address (i.e. message sender).
    pub originating_address: PduAddress,
    /// Message data coding scheme.
    pub dcs: DataCodingScheme,
    /// Message timestamp, from the service centre.
    pub scts: SmscTimestamp,
    /// User data.
    pub user_data: Vec<u8>,
    /// User data length.
    pub user_data_len: u8
}
impl DeliverPdu {
    /// Get the actual data (i.e. text or binary content) of the message.
    ///
    /// Methods on `GsmMessageData` let you convert this into actual text.
    pub fn get_message_data(&self) -> GsmMessageData {
        GsmMessageData {
            bytes: self.user_data.clone(),
            user_data_len: self.user_data_len,
            encoding: self.dcs.encoding(),
            udh: self.first_octet.udhi
        }
    }
}
impl<'a> TryFrom<&'a [u8]> for DeliverPdu {
    type Error = PDUError;
    fn try_from(b: &[u8]) -> PDUResult<Self> {
        if b.len() == 0 {
            return Err(PDUError::InvalidPdu("zero-length input"));
        }
        let scalen = b[0];
        let mut offset: usize = scalen as usize + 1;
        let sca = if scalen > 0 {
            let o = offset - 1;
            check_offset!(b, o, "SCA");
            Some(PduAddress::try_from(&b[0..offset])?)
        }
        else {
            None
        };
        check_offset!(b, offset, "first octet");
        let first_octet = DeliverPduFirstOctet::from(b[offset]);
        offset += 1;
        check_offset!(b, offset, "originating address len");
        let destination_len_nybbles = b[offset];
        // destination_len_nybbles represents the length of the address, in nybbles (half-octets).
        // Therefore, we divide by 2, rounding up, to get the number of full octets.
        let destination_len_octets = (destination_len_nybbles / 2) + destination_len_nybbles % 2;
        // destination_offset = what we're going to add to the offset to get the new offset
        // This is the destination length, in octets, plus one byte for the address length field,
        // and another because range syntax is non-inclusive.
        let destination_offset = (destination_len_octets as usize) + 2;
        let destination_end = offset + destination_offset;
        let de = destination_end - 1;
        check_offset!(b, de, "originating address");
        let originating_address = PduAddress::try_from(&b[offset..destination_end])?;
        offset += destination_offset;
        check_offset!(b, offset, "protocol identifier");
        let _pid = b[offset];
        offset += 1;
        check_offset!(b, offset, "data coding scheme");
        let dcs = DataCodingScheme::from(b[offset]);
        offset += 1;
        let scts_end = offset + 7;
        let ss = offset + 6;
        check_offset!(b, ss, "service center timestamp");
        let scts = SmscTimestamp::try_from(&b[offset..scts_end])?;
        offset += 7;
        check_offset!(b, offset, "user data len");
        let user_data_len = b[offset];
        offset += 1;
        let user_data = if b.get(offset).is_some() {
            b[offset..].to_owned()
        }
        else {
            vec![]
        };
        Ok(DeliverPdu {
            sca,
            first_octet,
            originating_address,
            dcs,
            scts,
            user_data,
            user_data_len
        })

    }
}

/// SMS delivery status codes for STATUS-REPORT PDUs.
#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive)]
pub enum MessageStatus {
    // Short message transaction completed
    /// Short message received by the SME
    ReceivedBySme = 0x00,
    /// Short message forwarded by the SC to the SME but the SC is unable to confirm delivery
    ForwardedUnconfirmed = 0x01,
    /// Short message replaced by the SC
    ReplacedBySc = 0x02,

    // Temporary error, SC still trying to transfer SM
    /// Congestion
    Congestion = 0x20,
    /// SME busy
    SmeBusy = 0x21,
    /// No response from SME
    NoResponseFromSme = 0x22,
    /// Service rejected
    ServiceRejected = 0x23,
    /// Quality of service not available
    QualityOfServiceNotAvailable = 0x24,
    /// Error in SME
    ErrorInSme = 0x25,

    // Permanent error, SC is not making any more transfer attempts
    /// Remote procedure error
    RemoteProcedureError = 0x40,
    /// Incompatible destination
    IncompatibleDestination = 0x41,
    /// Connection rejected by SME
    ConnectionRejectedBySme = 0x42,
    /// Not obtainable
    NotObtainable = 0x43,
    /// Quality of service not available
    QualityOfServiceNotAvailablePermanent = 0x44,
    /// No interworking available
    NoInterworkingAvailable = 0x45,
    /// SM Validity Period Expired
    SmValidityPeriodExpired = 0x46,
    /// SM Deleted by originating SME
    SmDeletedByOriginatingSme = 0x47,
    /// SM Deleted by SC Administration
    SmDeletedByScAdministration = 0x48,
    /// SM does not exist
    SmDoesNotExist = 0x49,

    // Temporary error, SC is not making any more transfer attempts
    /// Congestion
    CongestionNoMoreAttempts = 0x60,
    /// SME busy
    SmeBusyNoMoreAttempts = 0x61,
    /// No response from SME
    NoResponseFromSmeNoMoreAttempts = 0x62,
    /// Service rejected
    ServiceRejectedNoMoreAttempts = 0x63,
    /// Quality of service not available
    QualityOfServiceNotAvailableNoMoreAttempts = 0x64,
    /// Error in SME
    ErrorInSmeNoMoreAttempts = 0x65,
}

impl MessageStatus {
    /// Returns true if this status indicates successful delivery
    pub fn is_success(&self) -> bool {
        matches!(self, MessageStatus::ReceivedBySme | MessageStatus::ForwardedUnconfirmed | MessageStatus::ReplacedBySc)
    }

    /// Returns true if this is a temporary error (SC still trying)
    pub fn is_temporary_error(&self) -> bool {
        let status_code = *self as u8;
        (0x20..=0x3F).contains(&status_code)
    }

    /// Returns true if this is a permanent error (SC gave up).
    /// More delivery reports will not be received for the message.
    pub fn is_permanent_error(&self) -> bool {
        let status_code = *self as u8;
        (0x40..=0x6F).contains(&status_code)
    }
}

/// The first octet of a SMS-STATUS-REPORT PDU.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatusReportPduFirstOctet {
    /// Message type.
    pub mti: MessageType,
    /// More messages to send flag
    pub mms: bool,
    /// Loop prevention flag
    pub lp: bool,
    /// Status report qualifier (0 = result of SMS-SUBMIT, 1 = result of SMS-COMMAND)
    pub srq: bool,
    /// Does the user data segment contain a data header?
    pub udhi: bool,
}

impl From<u8> for StatusReportPduFirstOctet {
    fn from(b: u8) -> Self {
        let mti = MessageType::from_u8(b & 0b00000011)
            .expect("MessageType conversions should be exhaustive!");
        let mms = (b & 0b00000100) > 0;
        let lp = (b & 0b00001000) > 0;
        let srq = (b & 0b00100000) > 0;
        let udhi = (b & 0b01000000) > 0;

        StatusReportPduFirstOctet { mti, mms, lp, srq, udhi }
    }
}

/// An SMS-STATUS-REPORT PDU.
///
/// This PDU type is sent by the SMS Center to inform about the delivery status
/// of a previously submitted message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatusReportPdu {
    /// Service centre address, if provided here.
    pub sca: Option<PduAddress>,
    /// First octet (contains some extra fields).
    pub first_octet: StatusReportPduFirstOctet,
    /// Message reference (matches the reference from the original SMS-SUBMIT)
    pub message_reference: u8,
    /// Recipient address (destination of the original message)
    pub recipient_address: PduAddress,
    /// Service centre timestamp when the original message was received
    pub scts: SmscTimestamp,
    /// Discharge time - when the message was delivered or failed
    pub discharge_time: SmscTimestamp,
    /// Status of the message delivery attempt
    pub status: MessageStatus,
    /// Parameter indicating (optional) - only present if first_octet.udhi is true
    pub parameter_indicating: Option<u8>,
    /// User data (optional)
    pub user_data: Vec<u8>,
    /// User data length
    pub user_data_len: u8
}
impl StatusReportPdu {
    /// Get the actual data (i.e. text or binary content) of the optional user data.
    ///
    /// Methods on `GsmMessageData` let you convert this into actual text.
    /// Returns None if there's no user data.
    pub fn get_message_data(&self) -> Option<GsmMessageData> {
        if self.user_data.is_empty() {
            None
        } else {
            Some(GsmMessageData {
                bytes: self.user_data.clone(),
                user_data_len: self.user_data_len,
                encoding: MessageEncoding::Gsm7Bit, // Default encoding for status reports
                udh: self.first_octet.udhi
            })
        }
    }
}
impl<'a> TryFrom<&'a [u8]> for StatusReportPdu {
    type Error = PDUError;

    fn try_from(b: &[u8]) -> PDUResult<Self> {
        if b.is_empty() {
            return Err(PDUError::InvalidPdu("zero-length input"));
        }

        let scalen = b[0];
        let mut offset: usize = scalen as usize + 1;

        // Parse SCA if present
        let sca = if scalen > 0 {
            let o = offset - 1;
            check_offset!(b, o, "SCA");
            Some(PduAddress::try_from(&b[0..offset])?)
        } else {
            None
        };

        // Parse first octet
        check_offset!(b, offset, "first octet");
        let first_octet = StatusReportPduFirstOctet::from(b[offset]);
        offset += 1;

        // Parse message reference
        check_offset!(b, offset, "message reference");
        let message_reference = b[offset];
        offset += 1;

        // Parse recipient address
        check_offset!(b, offset, "recipient address len");
        let recipient_len_nybbles = b[offset];
        let recipient_len_octets = (recipient_len_nybbles / 2) + (recipient_len_nybbles % 2);
        let recipient_offset = (recipient_len_octets as usize) + 2;
        let recipient_end = offset + recipient_offset;
        let re = recipient_end - 1;
        check_offset!(b, re, "recipient address");
        let recipient_address = PduAddress::try_from(&b[offset..recipient_end])?;
        offset += recipient_offset;

        // Parse service centre timestamp (7 bytes)
        let scts_end = offset + 7;
        let ss = offset + 6;
        check_offset!(b, ss, "service center timestamp");
        let scts = SmscTimestamp::try_from(&b[offset..scts_end])?;
        offset += 7;

        // Parse discharge time (7 bytes)
        let discharge_end = offset + 7;
        let ds = offset + 6;
        check_offset!(b, ds, "discharge time");
        let discharge_time = SmscTimestamp::try_from(&b[offset..discharge_end])?;
        offset += 7;

        // Parse status
        check_offset!(b, offset, "status");
        let status = MessageStatus::from_u8(b[offset])
            .unwrap_or(MessageStatus::ErrorInSme); // Default to a reasonable error if unknown status
        offset += 1;

        // Parse optional parameter indicating (only if UDHI is set)
        let parameter_indicating = if first_octet.udhi && offset < b.len() {
            let pi = b[offset];
            offset += 1;
            Some(pi)
        } else {
            None
        };

        // Parse optional user data length and user data
        let (user_data_len, user_data) = if offset < b.len() {
            check_offset!(b, offset, "user data len");
            let udl = b[offset];
            offset += 1;

            let ud = if offset < b.len() {
                b[offset..].to_owned()
            } else {
                vec![]
            };

            (udl, ud)
        } else {
            (0, vec![])
        };

        Ok(StatusReportPdu {
            sca,
            first_octet,
            message_reference,
            recipient_address,
            scts,
            discharge_time,
            status,
            parameter_indicating,
            user_data,
            user_data_len,
        })
    }
}

/// An SMS-SUBMIT PDU.
///
/// **NB:** For simple usage, ignore 99% of the stuff in this module and just use
/// `Pdu::make_simple_message`!
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubmitPdu {
    /// Service centre address, if provided here.
    ///
    /// If you haven't set the service center address for all messages (see the `set_smsc_addr`
    /// function in `cmd::sms`), you'll need to provide it in SMS-SUBMIT PDUs using the `set_sca`
    /// method.
    pub sca: Option<PduAddress>,
    /// First octet (contains some extra fields).
    pub first_octet: PduFirstOctet,
    /// Message ID.
    ///
    /// This is set to 0 in `make_simple_message`. Presumably, you might ostensibly be able to use
    /// it to store outgoing messages in modem memory and then address them later?
    pub message_id: u8,
    /// Destination address (i.e. mesage recipient).
    pub destination: PduAddress,
    /// Message data coding scheme.
    pub dcs: DataCodingScheme,
    /// Validity period (used for message expiry).
    ///
    /// FIXME: as yet undocumented.
    pub validity_period: u8,
    /// User data.
    pub user_data: Vec<u8>,
    /// User data length.
    pub user_data_len: u8
}
impl SubmitPdu {
    /// Set the SMS service centre address.
    pub fn set_sca(&mut self, sca: PduAddress) {
        self.sca = Some(sca);
    }

    pub fn make_simple_message(recipient: PduAddress, msg: GsmMessageData) -> Self {
        SubmitPdu {
            sca: None,
            first_octet: PduFirstOctet {
                mti: MessageType::SmsSubmit,
                rd: false,
                vpf: VpFieldValidity::Invalid,
                rp: false,
                udhi: msg.udh,
                srr: false
            },
            message_id: 0,
            destination: recipient,
            dcs: DataCodingScheme::Standard {
                compressed: false,
                class: Some(MessageClass::StoreToNv),
                encoding: msg.encoding
            },
            validity_period: 0,
            user_data: msg.bytes,
            user_data_len: msg.user_data_len as u8
        }
    }
}
impl SubmitPdu {

    /// Convert to wire-format bytes, with a TPDU length value.
    pub fn as_bytes(&self) -> (Vec<u8>, usize) {
        let mut ret = vec![];

        // Handle SCA (Service Center Address)
        let sca_field_len = if let Some(ref sca) = self.sca {
            let sca_bytes = sca.as_bytes(false);
            ret.extend(&sca_bytes);
            sca_bytes.len()
        } else {
            ret.push(0); // SCA length = 0
            1
        };

        ret.push(self.first_octet.into());
        ret.push(self.message_id);
        ret.extend(self.destination.as_bytes(true));
        ret.push(0); // Protocol ID
        let dcs_byte = self.dcs.into();
        ret.push(dcs_byte);

        if self.first_octet.vpf != VpFieldValidity::Invalid {
            ret.push(self.validity_period);
        }

        ret.push(self.user_data_len);
        ret.extend(self.user_data.clone());

        // TPDU length excludes the entire SCA field (length byte + SCA data)
        let tpdu_len = ret.len() - sca_field_len;
        (ret, tpdu_len)
    }
}
