#![allow(dead_code)]

use std::cmp;
use std::io;

use encoding_rs::{Decoder, Encoding, UTF_8};

/// A BOM is at least 2 bytes and at most 3 bytes.
///
/// If fewer than 2 bytes are available to be read at the beginning of a
/// reader, then a BOM is `None`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bom {
    bytes: [u8; 3],
    len: usize,
}

impl Bom {
    fn as_slice(&self) -> &[u8] {
        &self.bytes[0..self.len]
    }
}

/// BomPeeker wraps `R` and satisfies the `io::Read` interface while also
/// providing a peek at the BOM if one exists. Peeking at the BOM does not
/// advance the reader.
struct BomPeeker<R> {
    rdr: R,
    bom: Option<Bom>,
    nread: usize,
}

impl<R: io::Read> BomPeeker<R> {
    /// Create a new BomPeeker.
    ///
    /// The first three bytes can be read using the `peek_bom` method, but
    /// will not advance the reader.
    fn new(rdr: R) -> BomPeeker<R> {
        BomPeeker { rdr: rdr, bom: None, nread: 0 }
    }

    /// Peek at the first three bytes of the underlying reader.
    ///
    /// This does not advance the reader provided by `BomPeeker`.
    ///
    /// If the underlying reader does not have at least two bytes available,
    /// then `None` is returned.
    fn peek_bom(&mut self) -> io::Result<Bom> {
        if let Some(bom) = self.bom {
            return Ok(bom);
        }
        self.bom = Some(Bom { bytes: [0; 3], len: 0 });
        let mut buf = [0u8; 3];
        let bom_len = try!(read_full(&mut self.rdr, &mut buf));
        self.bom = Some(Bom { bytes: buf, len: bom_len });
        Ok(self.bom.unwrap())
    }
}

impl<R: io::Read> io::Read for BomPeeker<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.nread < 3 {
            let bom = try!(self.peek_bom());
            let bom = bom.as_slice();
            if self.nread < bom.len() {
                let rest = &bom[self.nread..];
                let len = cmp::min(buf.len(), rest.len());
                buf[..len].copy_from_slice(&rest[..len]);
                self.nread += len;
                return Ok(len);
            }
        }
        let nread = try!(self.rdr.read(buf));
        self.nread += nread;
        Ok(nread)
    }
}

/// Like io::Read::read_exact, except it never returns UnexpectedEof and
/// instead returns the number of bytes read if EOF is seen before filling
/// `buf`.
fn read_full<R: io::Read>(
    mut rdr: R,
    mut buf: &mut [u8],
) -> io::Result<usize> {
    let mut nread = 0;
    while !buf.is_empty() {
        match rdr.read(buf) {
            Ok(0) => break,
            Ok(n) => {
                nread += n;
                let tmp = buf;
                buf = &mut tmp[n..];
            }
            Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(nread)
}

pub struct DecodeReader<R> {
    rdr: BomPeeker<R>,
    buf: Vec<u8>,
    buflen: usize,
    pos: usize,
    first: bool,
    decoder: Option<Decoder>,
}

impl<R: io::Read> DecodeReader<R> {
    pub fn new(rdr: R) -> DecodeReader<R> {
        DecodeReader {
            rdr: BomPeeker::new(rdr),
            buf: vec![0; 8 * (1<<10)],
            buflen: 0,
            pos: 0,
            first: true,
            decoder: None,
        }
    }
}

impl<R: io::Read> io::Read for DecodeReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.first {
            self.first = false;
            let bom = try!(self.rdr.peek_bom());
            let bom = bom.as_slice();
            if bom.len() >= 3 {
                if let Some((enc, _)) = Encoding::for_bom(bom) {
                    if enc != UTF_8 {
                        self.decoder = Some(enc.new_decoder());
                    }
                }
            }
        }
        if buf.is_empty() {
            return Ok(0);
        }
        let mut decoder = match self.decoder.as_mut() {
            None => return self.rdr.read(buf),
            Some(decoder) => decoder,
        };
        if self.pos >= self.buflen {
            self.buflen = try!(self.rdr.read(&mut self.buf));
            if self.buflen == 0 {
                return Ok(0);
            }
            // This is suspect.
            if self.buflen < 4 {
                self.buflen += try!(self.rdr.read(
                    &mut self.buf[self.buflen..]));
            }
            self.pos = 0;
        }
        let (res, ninput, noutput, _) = decoder.decode_to_utf8(
            &self.buf[self.pos..self.buflen], buf, false);
        self.pos += ninput;
        Ok(noutput)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;

    use super::{Bom, BomPeeker};

    #[test]
    fn peeker_empty() {
        let buf = [];
        let mut peeker = BomPeeker::new(&buf[..]);
        assert_eq!(Bom { bytes: [0; 3], len: 0}, peeker.peek_bom().unwrap());

        let mut tmp = [0; 100];
        assert_eq!(0, peeker.read(&mut tmp).unwrap());
    }

    #[test]
    fn peeker_one() {
        let buf = [1];
        let mut peeker = BomPeeker::new(&buf[..]);
        assert_eq!(
            Bom { bytes: [1, 0, 0], len: 1},
            peeker.peek_bom().unwrap());

        let mut tmp = [0; 100];
        assert_eq!(1, peeker.read(&mut tmp).unwrap());
        assert_eq!(1, tmp[0]);
        assert_eq!(0, peeker.read(&mut tmp).unwrap());
    }

    #[test]
    fn peeker_two() {
        let buf = [1, 2];
        let mut peeker = BomPeeker::new(&buf[..]);
        assert_eq!(
            Bom { bytes: [1, 2, 0], len: 2},
            peeker.peek_bom().unwrap());

        let mut tmp = [0; 100];
        assert_eq!(2, peeker.read(&mut tmp).unwrap());
        assert_eq!(1, tmp[0]);
        assert_eq!(2, tmp[1]);
        assert_eq!(0, peeker.read(&mut tmp).unwrap());
    }

    #[test]
    fn peeker_three() {
        let buf = [1, 2, 3];
        let mut peeker = BomPeeker::new(&buf[..]);
        assert_eq!(
            Bom { bytes: [1, 2, 3], len: 3},
            peeker.peek_bom().unwrap());

        let mut tmp = [0; 100];
        assert_eq!(3, peeker.read(&mut tmp).unwrap());
        assert_eq!(1, tmp[0]);
        assert_eq!(2, tmp[1]);
        assert_eq!(3, tmp[2]);
        assert_eq!(0, peeker.read(&mut tmp).unwrap());
    }

    #[test]
    fn peeker_four() {
        let buf = [1, 2, 3, 4];
        let mut peeker = BomPeeker::new(&buf[..]);
        assert_eq!(
            Bom { bytes: [1, 2, 3], len: 3},
            peeker.peek_bom().unwrap());

        let mut tmp = [0; 100];
        assert_eq!(3, peeker.read(&mut tmp).unwrap());
        assert_eq!(1, tmp[0]);
        assert_eq!(2, tmp[1]);
        assert_eq!(3, tmp[2]);
        assert_eq!(1, peeker.read(&mut tmp).unwrap());
        assert_eq!(4, tmp[0]);
        assert_eq!(0, peeker.read(&mut tmp).unwrap());
    }

    #[test]
    fn peeker_one_at_a_time() {
        let buf = [1, 2, 3, 4];
        let mut peeker = BomPeeker::new(&buf[..]);

        let mut tmp = [0; 1];
        assert_eq!(0, peeker.read(&mut tmp[..0]).unwrap());
        assert_eq!(0, tmp[0]);
        assert_eq!(1, peeker.read(&mut tmp).unwrap());
        assert_eq!(1, tmp[0]);
        assert_eq!(1, peeker.read(&mut tmp).unwrap());
        assert_eq!(2, tmp[0]);
        assert_eq!(1, peeker.read(&mut tmp).unwrap());
        assert_eq!(3, tmp[0]);
        assert_eq!(1, peeker.read(&mut tmp).unwrap());
        assert_eq!(4, tmp[0]);
    }
}
