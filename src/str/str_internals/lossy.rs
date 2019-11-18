// Exact copy of core::str::lossy.rs

use core::{mem, str as core_str};

use crate::str;

/// Lossy UTF-8 string.
pub struct Utf8Lossy {
    bytes: [u8],
}

impl Utf8Lossy {
    #[allow(clippy::transmute_ptr_to_ptr)]
    pub fn from_bytes(bytes: &[u8]) -> &Self {
        unsafe { mem::transmute(bytes) }
    }

    pub const fn chunks(&self) -> Utf8LossyChunksIter<'_> {
        Utf8LossyChunksIter {
            source: &self.bytes,
        }
    }
}

/// Iterator over lossy UTF-8 string
#[allow(missing_debug_implementations)]
pub struct Utf8LossyChunksIter<'a> {
    source: &'a [u8],
}

#[allow(single_use_lifetimes)]
#[derive(PartialEq, Eq, Debug)]
pub struct Utf8LossyChunk<'a> {
    /// Sequence of valid chars.
    /// Can be empty between broken UTF-8 chars.
    pub valid: &'a str,
    /// Single broken char, empty if none.
    /// Empty iff iterator item is last.
    pub broken: &'a [u8],
}

impl<'a> Iterator for Utf8LossyChunksIter<'a> {
    type Item = Utf8LossyChunk<'a>;

    fn next(&mut self) -> Option<Utf8LossyChunk<'a>> {
        const TAG_CONT_U8: u8 = 128;

        fn safe_get(xs: &[u8], i: usize) -> u8 {
            *xs.get(i).unwrap_or(&0)
        }

        if self.source.is_empty() {
            return None;
        }

        let mut i = 0;
        while i < self.source.len() {
            let i_ = i;

            let byte = unsafe { *self.source.get_unchecked(i) };
            i += 1;

            if byte < 128 {
            } else {
                let w = str::utf8_char_width(byte);

                macro_rules! error {
                    () => {{
                        unsafe {
                            let r = Utf8LossyChunk {
                                valid: core_str::from_utf8_unchecked(&self.source[0..i_]),
                                broken: &self.source[i_..i],
                            };
                            self.source = &self.source[i..];
                            return Some(r);
                        }
                    }};
                }

                match w {
                    2 => {
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                    }
                    3 => {
                        match (byte, safe_get(self.source, i)) {
                            (0xE0, 0xA0..=0xBF)
                            | (0xE1..=0xEC, 0x80..=0xBF)
                            | (0xED, 0x80..=0x9F)
                            | (0xEE..=0xEF, 0x80..=0xBF) => (),
                            _ => {
                                error!();
                            }
                        }
                        i += 1;
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                    }
                    4 => {
                        match (byte, safe_get(self.source, i)) {
                            (0xF0, 0x90..=0xBF)
                            | (0xF1..=0xF3, 0x80..=0xBF)
                            | (0xF4, 0x80..=0x8F) => (),
                            _ => {
                                error!();
                            }
                        }
                        i += 1;
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                        if safe_get(self.source, i) & 192 != TAG_CONT_U8 {
                            error!();
                        }
                        i += 1;
                    }
                    _ => {
                        error!();
                    }
                }
            }
        }

        let r = Utf8LossyChunk {
            valid: unsafe { core_str::from_utf8_unchecked(self.source) },
            broken: &[],
        };
        self.source = &[];
        Some(r)
    }
}
