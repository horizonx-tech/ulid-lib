use crate::base32::{self, DecodeError, ULID_LEN};
use std::fmt;
use std::str::FromStr;
/// Create a right-aligned bitmask of $len bits
macro_rules! bitmask {
    ($len:expr) => {
        ((1 << $len) - 1)
    };
}

/// A Ulid is a unique 128-bit lexicographically sortable identifier
///
/// Canonically, it is represented as a 26 character Crockford Base32 encoded
/// string.
///
/// Of the 128-bits, the first 48 are a unix timestamp in milliseconds. The
/// remaining 80 are random. The first 48 provide for lexicographic sorting and
/// the remaining 80 ensure that the identifier is unique.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Ulid(pub u128);

impl Ulid {
    /// The number of bits in a Ulid's time portion
    pub const TIME_BITS: u8 = 48;
    /// The number of bits in a Ulid's random portion
    pub const RAND_BITS: u8 = 80;

    /// Create a Ulid from separated parts.
    ///
    /// NOTE: Any overflow bits in the given args are discarded
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// let ulid = Ulid::from_string("01D39ZY06FGSCTVN4T2V9PKHFZ").unwrap();
    ///
    /// let ulid2 = Ulid::from_parts(ulid.timestamp_ms(), ulid.random());
    ///
    /// assert_eq!(ulid, ulid2);
    /// ```
    pub const fn from_parts(timestamp_ms: u64, random: u128) -> Ulid {
        let time_part = (timestamp_ms & bitmask!(Self::TIME_BITS)) as u128;
        let rand_part = random & bitmask!(Self::RAND_BITS);
        Ulid((time_part << Self::RAND_BITS) | rand_part)
    }

    /// Creates a Ulid from a Crockford Base32 encoded string
    ///
    /// An DecodeError will be returned when the given string is not formatted
    /// properly.
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// let text = "01D39ZY06FGSCTVN4T2V9PKHFZ";
    /// let result = Ulid::from_string(text);
    ///
    /// assert!(result.is_ok());
    /// assert_eq!(&result.unwrap().to_string(), text);
    /// ```
    pub const fn from_string(encoded: &str) -> Result<Ulid, base32::DecodeError> {
        match base32::decode(encoded) {
            Ok(int_val) => Ok(Ulid(int_val)),
            Err(err) => Err(err),
        }
    }

    /// The 'nil Ulid'.
    ///
    /// The nil Ulid is special form of Ulid that is specified to have
    /// all 128 bits set to zero.
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// let ulid = Ulid::nil();
    ///
    /// assert_eq!(
    ///     ulid.to_string(),
    ///     "00000000000000000000000000"
    /// );
    /// ```
    pub const fn nil() -> Ulid {
        Ulid(0)
    }

    pub const fn timestamp_ms(&self) -> u64 {
        (self.0 >> Self::RAND_BITS) as u64
    }

    /// Gets the random section of this ulid
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// let text = "01D39ZY06FGSCTVN4T2V9PKHFZ";
    /// let ulid = Ulid::from_string(text).unwrap();
    /// let ulid_next = ulid.increment().unwrap();
    ///
    /// assert_eq!(ulid.random() + 1, ulid_next.random());
    /// ```
    pub const fn random(&self) -> u128 {
        self.0 & bitmask!(Self::RAND_BITS)
    }

    /// Creates a Crockford Base32 encoded string that represents this Ulid
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// let text = "01D39ZY06FGSCTVN4T2V9PKHFZ";
    /// let ulid = Ulid::from_string(text).unwrap();
    ///
    /// let mut buf = [0; ulid::ULID_LEN];
    /// let new_text = ulid.to_str(&mut buf).unwrap();
    ///
    /// assert_eq!(new_text, text);
    /// ```
    #[deprecated(since = "1.2.0", note = "Use the infallible `array_to_str` instead.")]
    pub fn to_str<'buf>(&self, buf: &'buf mut [u8]) -> Result<&'buf mut str, base32::EncodeError> {
        #[allow(deprecated)]
        let len = base32::encode_to(self.0, buf)?;
        Ok(unsafe { core::str::from_utf8_unchecked_mut(&mut buf[..len]) })
    }

    /// Creates a Crockford Base32 encoded string that represents this Ulid
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// let text = "01D39ZY06FGSCTVN4T2V9PKHFZ";
    /// let ulid = Ulid::from_string(text).unwrap();
    ///
    /// let mut buf = [0; ulid::ULID_LEN];
    /// let new_text = ulid.array_to_str(&mut buf);
    ///
    /// assert_eq!(new_text, text);
    /// ```
    pub fn array_to_str<'buf>(&self, buf: &'buf mut [u8; ULID_LEN]) -> &'buf mut str {
        base32::encode_to_array(self.0, buf);
        unsafe { core::str::from_utf8_unchecked_mut(buf) }
    }

    pub fn to_string(&self) -> String {
        base32::encode(self.0)
    }

    /// Test if the Ulid is nil
    ///
    /// # Example
    /// ```rust
    /// use ulid::Ulid;
    ///
    /// # #[cfg(not(feature = "std"))]
    /// # let ulid = Ulid(1);
    /// # #[cfg(feature = "std")]
    /// let ulid = Ulid::new();
    /// assert!(!ulid.is_nil());
    ///
    /// let nil = Ulid::nil();
    /// assert!(nil.is_nil());
    /// ```
    pub const fn is_nil(&self) -> bool {
        self.0 == 0u128
    }

    /// Increment the random number, make sure that the ts millis stays the same
    pub const fn increment(&self) -> Option<Ulid> {
        const MAX_RANDOM: u128 = bitmask!(Ulid::RAND_BITS);

        if (self.0 & MAX_RANDOM) == MAX_RANDOM {
            None
        } else {
            Some(Ulid(self.0 + 1))
        }
    }

    /// Creates a Ulid using the provided bytes array.
    ///
    /// # Example
    /// ```
    /// use ulid::Ulid;
    /// let bytes = [0xFF; 16];
    ///
    /// let ulid = Ulid::from_bytes(bytes);
    ///
    /// assert_eq!(
    ///     ulid.to_string(),
    ///     "7ZZZZZZZZZZZZZZZZZZZZZZZZZ"
    /// );
    /// ```
    pub const fn from_bytes(bytes: [u8; 16]) -> Ulid {
        Self(u128::from_be_bytes(bytes))
    }

    /// Returns the bytes of the Ulid in big-endian order.
    ///
    /// # Example
    /// ```
    /// use ulid::Ulid;
    ///
    /// let text = "7ZZZZZZZZZZZZZZZZZZZZZZZZZ";
    /// let ulid = Ulid::from_string(text).unwrap();
    ///
    /// assert_eq!(ulid.to_bytes(), [0xFF; 16]);
    /// ```
    pub const fn to_bytes(&self) -> [u8; 16] {
        self.0.to_be_bytes()
    }
}

impl Default for Ulid {
    fn default() -> Self {
        Ulid::nil()
    }
}

impl From<Ulid> for String {
    fn from(ulid: Ulid) -> String {
        ulid.to_string()
    }
}

impl From<(u64, u64)> for Ulid {
    fn from((msb, lsb): (u64, u64)) -> Self {
        Ulid(u128::from(msb) << 64 | u128::from(lsb))
    }
}

impl From<Ulid> for (u64, u64) {
    fn from(ulid: Ulid) -> (u64, u64) {
        ((ulid.0 >> 64) as u64, (ulid.0 & bitmask!(64)) as u64)
    }
}

impl From<u128> for Ulid {
    fn from(value: u128) -> Ulid {
        Ulid(value)
    }
}

impl From<Ulid> for u128 {
    fn from(ulid: Ulid) -> u128 {
        ulid.0
    }
}

impl From<[u8; 16]> for Ulid {
    fn from(bytes: [u8; 16]) -> Self {
        Self(u128::from_be_bytes(bytes))
    }
}

impl From<Ulid> for [u8; 16] {
    fn from(ulid: Ulid) -> Self {
        ulid.0.to_be_bytes()
    }
}

impl FromStr for Ulid {
    type Err = DecodeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ulid::from_string(s)
    }
}

impl fmt::Display for Ulid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut buffer = [0; ULID_LEN];
        write!(f, "{}", self.array_to_str(&mut buffer))
    }
}

mod tests {
    use crate::base32::EncodeError;

    use super::*;

    #[test]
    fn test_static() {
        let s = Ulid(0x41414141414141414141414141414141).to_string();
        let u = Ulid::from_string(&s).unwrap();
        assert_eq!(&s, "21850M2GA1850M2GA1850M2GA1");
        assert_eq!(u.0, 0x41414141414141414141414141414141);
    }

    #[test]
    fn test_increment() {
        let ulid = Ulid::from_string("01BX5ZZKBKAZZZZZZZZZZZZZZZ").unwrap();
        let ulid = ulid.increment().unwrap();
        assert_eq!("01BX5ZZKBKB000000000000000", ulid.to_string());

        let ulid = Ulid::from_string("01BX5ZZKBKZZZZZZZZZZZZZZZX").unwrap();
        let ulid = ulid.increment().unwrap();
        assert_eq!("01BX5ZZKBKZZZZZZZZZZZZZZZY", ulid.to_string());
        let ulid = ulid.increment().unwrap();
        assert_eq!("01BX5ZZKBKZZZZZZZZZZZZZZZZ", ulid.to_string());
        assert!(ulid.increment().is_none());
    }

    #[test]
    fn test_increment_overflow() {
        let ulid = Ulid(u128::max_value());
        assert!(ulid.increment().is_none());
    }

    #[test]
    fn can_into_thing() {
        let ulid = Ulid::from_str("01FKMG6GAG0PJANMWFN84TNXCD").unwrap();
        let s: String = ulid.into();
        let u: u128 = ulid.into();
        let uu: (u64, u64) = ulid.into();
        let bytes: [u8; 16] = ulid.into();

        assert_eq!(Ulid::from_str(&s).unwrap(), ulid);
        assert_eq!(Ulid::from(u), ulid);
        assert_eq!(Ulid::from(uu), ulid);
        assert_eq!(Ulid::from(bytes), ulid);
    }

    #[test]
    fn default_is_nil() {
        assert_eq!(Ulid::default(), Ulid::nil());
    }

    #[test]
    fn can_display_things() {
        println!("{}", Ulid::nil());
        println!("{}", EncodeError::BufferTooSmall);
        println!("{}", DecodeError::InvalidLength);
        println!("{}", DecodeError::InvalidChar);
    }
}
