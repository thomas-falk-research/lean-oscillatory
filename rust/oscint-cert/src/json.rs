// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Strict JSON reading for certificates and the statement list.
//!
//! `serde_json` decides whether the text is JSON at all (it rejects `NaN`,
//! `Infinity`, trailing text, lone surrogates and nesting deeper than 128).
//! A second, small reader then walks the same text to keep what
//! `serde_json::Value` loses: the literal spelling of every number (so that
//! `1`, `1.0` and `1e0` are told apart without any floating point) and
//! duplicate object keys, which are refused. The two readings are compared
//! before the result is used.

use num_bigint::BigInt;
use serde_json::Value;

/// A JSON value with numbers kept as written.
#[derive(Debug, Clone, PartialEq)]
pub enum J {
    Null,
    Bool(bool),
    /// The number's literal text.
    Num(String),
    Str(String),
    Arr(Vec<J>),
    /// Members in source order; keys are unique.
    Obj(Vec<(String, J)>),
}

impl J {
    pub fn get(&self, key: &str) -> Option<&J> {
        match self {
            J::Obj(kv) => kv.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    /// A short name of the JSON type, for messages.
    pub fn type_name(&self) -> &'static str {
        match self {
            J::Null => "null",
            J::Bool(_) => "a boolean",
            J::Num(_) => "a JSON number",
            J::Str(_) => "a string",
            J::Arr(_) => "an array",
            J::Obj(_) => "an object",
        }
    }
    /// The value of a JSON integer: a number written without fraction or
    /// exponent. `None` for anything else, including `1.0` and `1e0`.
    pub fn as_integer(&self) -> Option<BigInt> {
        match self {
            J::Num(raw) => {
                let digits = raw.strip_prefix('-').unwrap_or(raw);
                if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
                    return None;
                }
                BigInt::parse_bytes(raw.as_bytes(), 10)
            }
            _ => None,
        }
    }
}

struct Reader<'a> {
    text: &'a str,
    b: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn ws(&mut self) {
        while let Some(c) = self.b.get(self.i) {
            if matches!(c, b' ' | b'\t' | b'\n' | b'\r') {
                self.i += 1;
            } else {
                break;
            }
        }
    }

    fn expect(&mut self, c: u8) -> Result<(), String> {
        if self.b.get(self.i) == Some(&c) {
            self.i += 1;
            Ok(())
        } else {
            Err(format!("expected '{}' at byte {}", c as char, self.i))
        }
    }

    fn literal(&mut self, word: &str, value: J) -> Result<J, String> {
        if self.b[self.i..].starts_with(word.as_bytes()) {
            self.i += word.len();
            Ok(value)
        } else {
            Err(format!("unexpected token at byte {}", self.i))
        }
    }

    fn string(&mut self) -> Result<String, String> {
        let start = self.i;
        self.expect(b'"')?;
        loop {
            match self.b.get(self.i) {
                None => return Err("unterminated string".into()),
                Some(b'\\') => self.i += 2,
                Some(b'"') => {
                    self.i += 1;
                    break;
                }
                Some(_) => self.i += 1,
            }
        }
        let raw = self
            .text
            .get(start..self.i)
            .ok_or_else(|| "string boundary".to_string())?;
        serde_json::from_str::<String>(raw).map_err(|e| format!("bad string: {e}"))
    }

    fn value(&mut self, depth: usize) -> Result<J, String> {
        if depth > 200 {
            return Err("nesting too deep".into());
        }
        self.ws();
        match self.b.get(self.i).copied() {
            None => Err("unexpected end of text".into()),
            Some(b'{') => {
                self.i += 1;
                let mut members: Vec<(String, J)> = Vec::new();
                self.ws();
                if self.b.get(self.i) == Some(&b'}') {
                    self.i += 1;
                    return Ok(J::Obj(members));
                }
                loop {
                    self.ws();
                    let key = self.string()?;
                    self.ws();
                    self.expect(b':')?;
                    let v = self.value(depth + 1)?;
                    if members.iter().any(|(k, _)| *k == key) {
                        return Err(format!("duplicate object key {key:?}"));
                    }
                    members.push((key, v));
                    self.ws();
                    match self.b.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {
                            self.i += 1;
                            return Ok(J::Obj(members));
                        }
                        _ => return Err(format!("expected ',' or '}}' at byte {}", self.i)),
                    }
                }
            }
            Some(b'[') => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws();
                if self.b.get(self.i) == Some(&b']') {
                    self.i += 1;
                    return Ok(J::Arr(items));
                }
                loop {
                    items.push(self.value(depth + 1)?);
                    self.ws();
                    match self.b.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b']') => {
                            self.i += 1;
                            return Ok(J::Arr(items));
                        }
                        _ => return Err(format!("expected ',' or ']' at byte {}", self.i)),
                    }
                }
            }
            Some(b'"') => Ok(J::Str(self.string()?)),
            Some(b't') => self.literal("true", J::Bool(true)),
            Some(b'f') => self.literal("false", J::Bool(false)),
            Some(b'n') => self.literal("null", J::Null),
            Some(_) => {
                let start = self.i;
                while let Some(c) = self.b.get(self.i) {
                    if matches!(c, b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
                        self.i += 1;
                    } else {
                        break;
                    }
                }
                if self.i == start {
                    return Err(format!("unexpected character at byte {start}"));
                }
                let raw = self
                    .text
                    .get(start..self.i)
                    .ok_or_else(|| "number boundary".to_string())?;
                Ok(J::Num(raw.to_string()))
            }
        }
    }
}

/// Both readings must describe the same value.
fn agree(j: &J, v: &Value) -> bool {
    match (j, v) {
        (J::Null, Value::Null) => true,
        (J::Bool(a), Value::Bool(b)) => a == b,
        (J::Num(raw), Value::Number(n)) => {
            if let Some(i) = n.as_i64() {
                raw.parse::<i64>() == Ok(i)
            } else if let Some(u) = n.as_u64() {
                raw.parse::<u64>() == Ok(u)
            } else {
                true // a float in serde_json's reading; the literal text is what counts
            }
        }
        (J::Str(a), Value::String(b)) => a == b,
        (J::Arr(a), Value::Array(b)) => a.len() == b.len() && a.iter().zip(b).all(|(x, y)| agree(x, y)),
        (J::Obj(a), Value::Object(b)) => {
            a.len() == b.len() && a.iter().all(|(k, x)| b.get(k).is_some_and(|y| agree(x, y)))
        }
        _ => false,
    }
}

/// Reads one JSON document, strictly.
pub fn parse(text: &str) -> Result<J, String> {
    let v: Value = serde_json::from_str(text).map_err(|e| format!("not valid JSON: {e}"))?;
    let mut r = Reader {
        text,
        b: text.as_bytes(),
        i: 0,
    };
    let j = r.value(0)?;
    r.ws();
    if r.i != r.b.len() {
        return Err("text after the JSON value".into());
    }
    if !agree(&j, &v) {
        return Err("the two JSON readers disagree".into());
    }
    Ok(j)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_keep_their_spelling() {
        let j =
            parse(r#"{"a": 1, "b": 1.0, "c": 1e0, "d": -0, "e": -12, "f": 123456789012345678901234567890}"#)
                .expect("valid");
        assert_eq!(j.get("a").and_then(J::as_integer), Some(BigInt::from(1)));
        assert_eq!(j.get("b").and_then(J::as_integer), None);
        assert_eq!(j.get("c").and_then(J::as_integer), None);
        assert_eq!(j.get("d").and_then(J::as_integer), Some(BigInt::from(0)));
        assert_eq!(j.get("e").and_then(J::as_integer), Some(BigInt::from(-12)));
        assert_eq!(
            j.get("f").and_then(J::as_integer).map(|v| v.to_string()),
            Some("123456789012345678901234567890".to_string())
        );
        assert_eq!(J::Str("1".into()).as_integer(), None);
        assert_eq!(J::Bool(true).as_integer(), None);
    }

    #[test]
    fn invalid_json_is_refused() {
        for text in [
            "",
            "{",
            "[1,]",
            "{\"a\":1,}",
            "NaN",
            "Infinity",
            "-Infinity",
            "{\"a\": NaN}",
            "{\"a\": Infinity}",
            "01",
            "1.",
            ".5",
            "+1",
            "{'a': 1}",
            "{\"a\": 1} x",
            "\"\\ud800\"",
            "{\"a\": 1e999}",
            "[1 2]",
            "nul",
            "{\"a\" 1}",
            "\u{feff}{}",
        ] {
            assert!(parse(text).is_err(), "{text:?} must be refused");
        }
    }

    #[test]
    fn duplicate_keys_are_refused() {
        assert!(parse(r#"{"a": 1, "a": 2}"#).is_err());
        assert!(parse(r#"{"a": 1, "\u0061": 2}"#).is_err());
        assert!(parse(r#"{"x": {"k": 1, "k": 1}}"#).is_err());
        assert!(parse(r#"[{"k": null, "k": null}]"#).is_err());
        assert!(parse(r#"{"a": 1, "A": 2}"#).is_ok());
    }

    #[test]
    fn structure_is_preserved() {
        let j = parse(" { \"s\" : \"a\\n\\\"\\u00e9\\\\\" , \"l\" : [ true , false , null , [ ] , { } ] } ")
            .expect("valid");
        assert_eq!(j.get("s"), Some(&J::Str("a\n\"é\\".into())));
        assert_eq!(
            j.get("l"),
            Some(&J::Arr(vec![
                J::Bool(true),
                J::Bool(false),
                J::Null,
                J::Arr(vec![]),
                J::Obj(vec![])
            ]))
        );
        // deep nesting is refused by serde_json's recursion limit
        let deep = format!("{}{}", "[".repeat(500), "]".repeat(500));
        assert!(parse(&deep).is_err());
    }
}
