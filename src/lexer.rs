use std::io;
use std::fs::File;
use std::mem;
use std::path::Path;
use num::{rational::Ratio, BigInt, BigRational};
use unicode_reader::CodePoints;
use crate::tokens::TokenTable;
use crate::types::{KToken, Name};

fn is_letter_like_unicode(c: char) -> bool {
    ('α' <= c && c <= 'ω' && c != 'λ') ||    // Lower greek, except lambda
    ('Α' <= c && c <= 'Ω' && c != 'Π' && c != 'Σ') || // Upper greek, except Pi and Sigma
    ('ϊ' <= c && c <= 'ϻ') ||                // Coptic letters
    ('ἀ' <= c && c <= '῾') ||                // Polytonic Greek Extended Character Set
    ('℀' <= c && c <= '⅏') ||                // Letter like block
    ('𝒜' <= c && c <= '𝖟')                 // Latin letters, Script, Double-struck, Fractur
}

fn is_sub_script_alnum_unicode(c: char) -> bool {
    ('ⁿ' <= c && c <= '₉') || // n superscript and numberic subscripts
    ('ₐ' <= c && c <= 'ₜ') || // letter-like subscripts
    ('ᵢ' <= c && c <= 'ᵪ')    // letter-like subscripts
}

fn is_id_first(c: char) -> bool {
    c.is_alphabetic() || c == '_' || c == '«' || is_letter_like_unicode(c)
}

fn is_id_rest(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' ||
    is_letter_like_unicode(c) || is_sub_script_alnum_unicode(c)
}

#[derive(Debug, PartialEq)] pub enum Token {
    Keyword(String, u32),
    CommandKeyword(String),
    Identifier(Name),
    Numeral(BigInt),
    Decimal(BigRational),
    StringTk(String),
    Char(char),
    QuotedSymbol(String),
    DocBlock(bool, String),
    FieldNum(u32),
    FieldName(Name),
    Eof
}

impl Token {
    pub fn is_tk(&self, s: &str) -> bool {
        match self {
            Token::Keyword(s2, _) => s == s2,
            Token::CommandKeyword(s2) => s == s2,
            _ => false
        }
    }

    pub fn tk(&self) -> Option<&str> {
        match self {
            Token::Keyword(s, _) => Some(s),
            Token::CommandKeyword(s) => Some(s),
            _ => None
        }
    }
}

fn invalid(s: &str) -> io::Error { io::Error::new(io::ErrorKind::InvalidData, s) }
fn throw<A>(s: &str) -> io::Result<A> { Err(invalid(s)) }

struct LexerCore<T: Iterator<Item = io::Result<char>>> {
    source: T,
    pushback: Vec<char>,
    curr: char,
    in_notation: bool,
    allow_field_notation: bool
}

impl<T: Iterator<Item = io::Result<char>>> LexerCore<T> {
    fn next(&mut self) -> io::Result<char> {
        self.curr =
            if let Some(pb) = self.pushback.pop() {pb}
            else if let Some(ch) = self.source.next() {ch?}
            else {'\0'};
        Ok(self.curr)
    }

    pub fn new(mut source: T) -> io::Result<Self> {
        let curr = if let Some(ch) = source.next() {ch?} else {'\0'};
        Ok(LexerCore {source, pushback: Vec::new(),
            curr, in_notation: false, allow_field_notation: true})
    }

    fn pushback(&mut self, last: char) {
        println!("{:?}, {:?}", self.pushback, self.curr);
        self.pushback.push(self.curr);
        self.curr = last;
        println!("{:?}, {:?} <- {:?}", self.pushback, self.curr, last);
    }

    fn read_number(&mut self) -> io::Result<Token> {
        let mut num = (self.curr as u32) - ('0' as u32);

        let base = if num == 0 {
            let base = match self.next()? {
                'B' | 'b' => 2,
                'O' | 'o' => 8,
                'X' | 'x' => 16,
                _ => 10
            };
            if base != 10 {
                num = self.next()?.to_digit(base)
                    .ok_or_else(|| invalid("invalid numeral, expected digit after base prefix"))?;
            }
            base
        } else {10};

        let mut num: BigInt = num.into();
        let mut denom: Option<BigInt> = None;
        loop {
            if let Some(val) = self.curr.to_digit(base) {
                num = base*num + val;
                match &mut denom { Some(q) => *q *= 10, None => () };
                self.next()?;
            } else if base == 10 && self.curr == '.' {
                if !self.next()?.is_digit(base) || denom.is_some() {
                    self.pushback('.'); break
                }
                denom = Some(1.into());
            } else {break}
        }
        match denom {
            Some(denom) => Ok(Token::Decimal(Ratio::new(num, denom))),
            None => Ok(Token::Numeral(num))
        }
    }

    fn read_line_comment(&mut self) -> io::Result<()> {
        loop {
            match self.curr {
                '\0' => return Ok(()),
                '\n' => {self.next()?; return Ok(())},
                _ => self.next()?
            };
        }
    }

    fn read_block_comment(&mut self) -> io::Result<()> {
        let mut nest = 1;
        loop {
            match self.curr {
                '\0' => return throw("unexpected end of comment block"),
                '/' => if self.next()? == '-' {
                    self.next()?; nest += 1;
                },
                '-' => if self.next()? == '/' {
                    nest -= 1;
                    if nest == 0 { self.next()?; return Ok(()) }
                },
                _ => { self.next()?; }
            }
        }
    }

    fn read_doc_block(&mut self, modd: bool) -> io::Result<Token> {
        let mut buf = String::new();
        loop {
            let c = self.curr;
            match c {
                '\0' => return throw("unexpected end of documentation block"),
                '-' => if self.next()? == '/' {
                    self.next()?; return Ok(Token::DocBlock(modd, buf))
                },
                _ => { self.next()?; }
            };
            buf.push(c);
        }
    }

    fn read_single_char(&mut self, err_msg: &str) -> io::Result<char> {
        match self.curr {
            '\0' => { throw(err_msg) },
            '\\' => match self.next()? {
                '\0' => { throw(err_msg) },
                'n' => { self.next()?; Ok('\n') },
                't' => { self.next()?; Ok('\t') },
                '\'' => { self.next()?; Ok('\'') },
                '\"' => { self.next()?; Ok('\"') },
                '\\' => { self.next()?; Ok('\\') },
                'x' => {
                    let hex = self.next()?.to_digit(16).ok_or_else(|| invalid("invalid hex char in escape sequence"))?;
                    let hex = 16*hex + self.next()?.to_digit(16).ok_or_else(|| invalid("invalid hex char in escape sequence"))?;
                    std::char::from_u32(hex).ok_or_else(|| invalid("invalid utf-8")) },
                'u' => {
                    let hex = self.next()?.to_digit(16).ok_or_else(|| invalid("invalid hex char in escape sequence"))?;
                    let hex = 16*hex + self.next()?.to_digit(16).ok_or_else(|| invalid("invalid hex char in escape sequence"))?;
                    let hex = 16*hex + self.next()?.to_digit(16).ok_or_else(|| invalid("invalid hex char in escape sequence"))?;
                    let hex = 16*hex + self.next()?.to_digit(16).ok_or_else(|| invalid("invalid hex char in escape sequence"))?;
                    std::char::from_u32(hex).ok_or_else(|| invalid("invalid utf-8")) },
                _ => throw("invalid escape sequence")
            },
            c => { self.next()?; Ok(c) }
        }
    }

    fn read_char(&mut self) -> io::Result<Token> {
        let c = self.read_single_char("unexpected end of character")?;
        if self.curr != '\'' {return throw("invalid character, ' expected")}
        self.next()?; Ok(Token::Char(c))
    }

    fn read_string(&mut self) -> io::Result<Token> {
        let mut s = String::new(); self.next()?;
        loop {
            if self.curr == '\"' {
                self.next()?; return Ok(Token::StringTk(s)) }
            s.push(self.read_single_char("unexpected end of string")?);
        }
    }

    fn read_quoted_symbol(&mut self) -> io::Result<Token> {
        let mut s = String::new(); self.next()?;
        let mut start = false;
        let mut trailing_space = false;
        loop {
            match self.curr {
                '\0' => return throw("unexpected quoted identifier"),
                '`' if start => return throw("empty quoted identifier"),
                '`' => return Ok(Token::QuotedSymbol(s)),
                '\"' | '\n' | '\t' => return throw("invalid character in quoted identifier"),
                ' ' => { if !start {trailing_space = true}; s.push(' ') },
                c if start && c.is_digit(10) => return throw("quoted identifier can't start with digit"),
                _ if trailing_space => return throw("unexpected space inside of quoted symbol"),
                c => { start = false; s.push(c) },
            }
            self.next()?;
        }
    }

    fn read_field_idx(&mut self) -> io::Result<Token> {
        let mut num: u32 = 0;
        while let Some(m) = self.curr.to_digit(10) {
            num = num.checked_mul(10).and_then(|n| n.checked_add(m))
                .ok_or_else(|| invalid("field notation index too large"))?;
            self.next()?;
        }
        Ok(Token::FieldNum(num))
    }

    fn read_id_part(&mut self, cs: &mut String) -> io::Result<()> {
        let mut escaped = false;
        loop {
            if escaped {
                match self.curr {
                    '»' => escaped = false,
                    '\r' | '\t' | '\n' | '«' => return throw("illegal character in escaped identifier"),
                    _ => ()
                }
            } else {
                match self.curr {
                    '«' => escaped = true,
                    c if is_id_rest(c) => (),
                    _ => return Ok(())
                }
            }
            cs.push(self.curr);
            self.next()?;
        }
    }

    fn munch<'a>(&mut self, tt: &'a TokenTable, cs: &mut String) -> io::Result<Option<(&'a KToken, usize)>> {
        let mut res = tt.search().next(cs);
        loop {
            match res {
                Ok(tk) => return Ok(tk),
                Err(iter) => {
                    let len = cs.len();
                    let c = self.next()?;
                    if c == '\0' {return Ok(iter.finish())}
                    cs.push(c);
                    res = iter.next(&cs[len..]);
                }
            }
        }
    }

    fn read_key_cmd_id(&mut self, tt: &TokenTable) -> io::Result<Token> {
        let mut cs = String::new();

        fn cs_to_name(cs: &str) -> Name {
            let mut n: Name = Name::anon();
            let mut part = String::new();
            let mut escaped = false;
            for c in cs.chars() {
                match c {
                    '«' => escaped = true,
                    '»' => escaped = false,
                    '.' if !escaped =>
                        n = n.str(mem::replace(&mut part, String::new())),
                    c => part.push(c)
                }
            }
            n.str(part)
        }

        let mut id_sz = 0;
        if self.allow_field_notation && self.curr == '.' {
            if self.next()?.is_digit(10) {return self.read_field_idx()}
            if is_id_first(self.curr) && self.curr != '_' {
                self.read_id_part(&mut cs)?;
                return Ok(Token::FieldName(cs_to_name(&cs)))
            }
            cs.push('.');
        } else {
            while is_id_first(self.curr) {
                self.read_id_part(&mut cs)?;
                id_sz = cs.len();
                if self.curr != '.' {break}
                cs.push('.');
                self.next()?;
            }
        }
        cs.push(self.curr);

        let (tk, n) = match self.munch(tt, &mut cs)?.and_then(|(tk, n)| {
            if n/2 < id_sz {None} else {Some((tk, n/2))}
        }) {
            None => (Token::Identifier(cs_to_name(&cs[0..id_sz])), id_sz),
            Some((KToken {tk, prec: None}, n)) => (Token::CommandKeyword(tk.clone()), n),
            Some((KToken {tk, prec: Some(prec)}, n)) => (Token::Keyword(tk.clone(), *prec), n)
        };
        if n == 0 {return throw("unexpected token")}
        for c in cs.split_at(n).1.chars().rev().skip(1) { self.pushback(c) }
        Ok(tk)
    }

    pub fn lex(&mut self, tt: &TokenTable) -> io::Result<Token> {
        loop {
            match self.curr {
                '\0' => return Ok(Token::Eof),
                ' ' | '\r' | '\t' | '\n' => (),
                '\"' => return self.read_string(),
                '`' if self.in_notation => return self.read_quoted_symbol(),
                c if c.is_digit(10) => return self.read_number(),
                _ => {
                    match self.read_key_cmd_id(tt)? {
                        Token::Keyword(s, prec) => match s.as_ref() {
                            "--" => self.read_line_comment()?,
                            "/-" => self.read_block_comment()?,
                            "/--" => return self.read_doc_block(false),
                            "/-!" => return self.read_doc_block(true),
                            "\'" => return self.read_char(),
                            _ => return Ok(Token::Keyword(s, prec)) },
                        k => return Ok(k) }
                } }
            self.next()?;
        }
    }
}

pub struct Lexer<T: io::Read> {
    pub token_table: TokenTable,
    data: LexerCore<CodePoints<io::Bytes<T>>>
}

pub fn from_file(path: &Path, tt: TokenTable) -> io::Result<Lexer<io::BufReader<File>>> {
    Lexer::new(io::BufReader::new(File::open(path)?), tt)
}

impl<T: io::Read> Lexer<T> {
    pub fn new(source: T, token_table: TokenTable) -> io::Result<Self> {
        Ok(Lexer {token_table, data: LexerCore::new(CodePoints::from(source))?})
    }

    pub fn curr(&self) -> char { self.data.curr }

    pub fn lex(&mut self) -> io::Result<Token> {
        let tk = self.data.lex(&self.token_table);
        println!("lex {:?}", tk);
        tk
    }

    pub fn allow_field_notation(&mut self, flag: bool) -> bool {
        mem::replace(&mut self.data.allow_field_notation, flag)
    }
}

impl<T: io::Read> Iterator for Lexer<T> {
    type Item = io::Result<Token>;

    fn next(&mut self) -> Option<io::Result<Token>> {
        if self.curr() == '\0' {return None}
        match self.lex() {
            Err(err) => Some(Err(err)),
            Ok(Token::Eof) => None,
            Ok(tk) => Some(Ok(tk))
        }
    }
}
