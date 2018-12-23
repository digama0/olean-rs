use std::io;
use std::fs::File;
use std::rc::Rc;
use std::mem;
use std::path::Path;
use radix_trie::{Trie, TrieCommon};
use num::{rational::Ratio, BigInt, BigRational};
use unicode_reader::CodePoints;
use super::loader::Loader;
use super::types::{Modification, Token, Name, Name2};

static MAX_PREC: u32 = 1024;
static ARROW_PREC: u32 = 25;
static PLUS_PREC: u32 = 65;
static TOKENS: &[(&str, u32)] = &[
    ("fun", 0), ("Pi", 0), ("let", 0), ("in", 0), ("at", 0),
    ("have", 0), ("assume", 0), ("show", 0), ("suffices", 0),
    ("do", 0), ("if", 0), ("then", 0), ("else", 0), ("by", 0),
    ("hiding", 0), ("replacing", 0), ("renaming", 0),
    ("from", 0), ("(", MAX_PREC), ("`(", MAX_PREC), ("``(", MAX_PREC),
    ("```(", MAX_PREC), ("`[", MAX_PREC), ("`", MAX_PREC),
    ("%%", MAX_PREC), ("()", MAX_PREC), ("(::)", MAX_PREC), (")", 0), ("'", 0),
    ("{", MAX_PREC), ("}", 0), ("_", MAX_PREC),
    ("[", MAX_PREC), ("#[", MAX_PREC), ("]", 0), ("⦃", MAX_PREC), ("⦄", 0), (".(", 0),
    ("{!", MAX_PREC), ("!}", 0),
    ("Type", MAX_PREC), ("Type*", MAX_PREC), ("Sort", MAX_PREC), ("Sort*", MAX_PREC),
    ("(:", MAX_PREC), (":)", 0), (".(", MAX_PREC), ("._", MAX_PREC),
    ("⟨", MAX_PREC), ("⟩", 0), ("^", 0),
    ("//", 0), ("|", 0), ("with", 0), ("without", 0), ("..", 0), ("...", 0), (",", 0),
    (".", 0), (":", 0), ("!", 0), ("calc", 0), (":=", 0), ("--", 0), ("#", MAX_PREC),
    ("/-", 0), ("/--", 0), ("/-!", 0), ("begin", MAX_PREC), ("using", 0),
    ("@@", MAX_PREC), ("@", MAX_PREC),
    ("sorry", MAX_PREC), ("+", PLUS_PREC), ("->", ARROW_PREC), ("<-", 0),
    ("match", 0), ("^.", MAX_PREC+1),
    ("renaming", 0), ("extends", 0)];

static COMMANDS: &[&str] = &[
    "theorem", "axiom", "axioms", "variable", "protected", "private", "hide",
    "definition", "meta", "mutual", "example", "noncomputable", "abbreviation",
    "variables", "parameter", "parameters", "constant", "constants",
    "using_well_founded", "[whnf]",
    "end", "namespace", "section", "prelude",
    "import", "inductive", "coinductive", "structure", "class", "universe", "universes", "local",
    "precedence", "reserve", "infixl", "infixr", "infix", "postfix", "prefix", "notation",
    "set_option", "open", "export", "@[",
    "attribute", "instance", "include", "omit", "init_quotient",
    "declare_trace", "add_key_equivalence",
    "run_cmd", "#check", "#reduce", "#eval", "#print", "#help", "#exit",
    "#compile", "#unify"];

static ALIASES: &[(&str, &str, Option<u32>)] = &[
    ("λ", "fun", Some(0)),
    ("forall", "Pi", Some(0)), ("∀", "Pi", Some(0)), ("Π", "Pi", Some(0)),
    ("(|", "⟨", Some(MAX_PREC)), ("|)", "⟩", Some(0)),
    ("→", "->", Some(ARROW_PREC)), ("←", "<-", Some(0)),
    ("lemma", "theorem", None), ("def", "definition", None)];

fn is_letter_like_unicode(c: char) -> bool {
    ('α' <= c && c <= 'ω' && c != 'λ') ||    // Lower greek, but lambda
    ('Α' <= c && c <= 'Ω' && c != 'Π' && c != 'Σ') || // Upper greek, but Pi and Sigma
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

#[derive(Debug)] pub struct TokenTable(Trie<String, Token>);

impl TokenTable {
    fn new() -> TokenTable {
        let mut table = TokenTable(Trie::new());
        for (s, prec) in TOKENS {
            table.insert(Token{tk: s.to_string(), prec: Some(*prec)}) }
        for s in COMMANDS {
            table.insert(Token{tk: s.to_string(), prec: None}) }
        for (s1, s2, prec) in ALIASES {
            table.0.insert(s1.to_string(), Token{tk: s2.to_string(), prec: *prec}); }
        table
    }

    fn insert(&mut self, tk: Token) {
        self.0.insert(tk.tk.clone(), tk);
    }
}

impl<'a> IntoIterator for &'a TokenTable {
    type Item = &'a Token;
    type IntoIter = radix_trie::iter::Values<'a, String, Token>;
    fn into_iter(self) -> Self::IntoIter { self.0.values() }
}

pub fn get_token_table(load: &mut Loader) -> io::Result<TokenTable> {
    let Loader{map, order} = load;
    let mut table = TokenTable::new();
    for n in order {
        let mods = Loader::get_mods(map, n.clone())?;
        for m in mods {
            match m {
                Modification::Token(tk) => table.insert(tk.clone()),
                _ => ()
            }
        }
    }
    Ok(table)
}

pub struct Scanner<T: Iterator<Item = io::Result<char>>> {
    source: T,
    token_table: TokenTable,
    pushback: Vec<char>,
    curr: char,
    in_notation: bool,
    allow_field_notation: bool
}

pub type FileScanner = Scanner<CodePoints<io::Bytes<io::BufReader<File>>>>;
pub fn from_file(path: &Path, token_table: TokenTable) -> io::Result<FileScanner> {
    Scanner::new(CodePoints::from(io::BufReader::new(File::open(path)?)), token_table)
}

#[derive(Debug)] pub enum SToken {
    Keyword(String, u32),
    CommandKeyword(String),
    Identifier(Name),
    Numeral(BigInt),
    Decimal(BigRational),
    String(String),
    Char(char),
    QuotedSymbol(String),
    DocBlock(bool, String),
    FieldNum(u32),
    FieldName(Name),
    Eof
}

fn invalid(s: &str) -> io::Error { io::Error::new(io::ErrorKind::InvalidData, s) }
fn throw<A>(s: &str) -> io::Result<A> { Err(invalid(s)) }

enum TryPrefix { Done, Next }

impl<T: Iterator<Item = io::Result<char>>> Scanner<T> {
    fn next(&mut self) -> io::Result<char> {
        self.curr =
            if let Some(pb) = self.pushback.pop() {pb}
            else if let Some(ch) = self.source.next() {ch?}
            else {'\0'};
        Ok(self.curr)
    }

    pub fn new(mut source: T, token_table: TokenTable) -> io::Result<Self> {
        let curr = if let Some(ch) = source.next() {ch?} else {'\0'};
        Ok(Scanner {source, token_table, pushback: Vec::new(),
            curr, in_notation: false, allow_field_notation: true})
    }

    fn pushback(&mut self, last: char) {
        println!("{:?}, {:?}", self.pushback, self.curr);
        self.pushback.push(self.curr);
        self.curr = last;
        println!("{:?}, {:?} <- {:?}", self.pushback, self.curr, last);
    }

    fn read_number(&mut self) -> io::Result<SToken> {
        let mut num = (self.curr as u32) - ('0' as u32);

        let base = if num == 0 {
            let base = match self.next()? {
                'b' => 2,
                'B' => 2,
                'O' => 8,
                'o' => 8,
                'X' => 16,
                'x' => 16,
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
            Some(denom) => Ok(SToken::Decimal(Ratio::new(num, denom))),
            None => Ok(SToken::Numeral(num))
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

    fn read_doc_block(&mut self, modd: bool) -> io::Result<SToken> {
        let mut buf = String::new();
        loop {
            let c = self.curr;
            match c {
                '\0' => return throw("unexpected end of documentation block"),
                '-' => if self.next()? == '/' {
                    self.next()?; return Ok(SToken::DocBlock(modd, buf))
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

    fn read_char(&mut self) -> io::Result<SToken> {
        let c = self.read_single_char("unexpected end of character")?;
        if self.curr != '\'' {return throw("invalid character, ' expected")}
        self.next()?; Ok(SToken::Char(c))
    }

    fn read_string(&mut self) -> io::Result<SToken> {
        let mut s = String::new(); self.next()?;
        loop {
            if self.curr == '\"' {
                self.next()?; return Ok(SToken::String(s)) }
            s.push(self.read_single_char("unexpected end of string")?);
        }
    }

    fn read_quoted_symbol(&mut self) -> io::Result<SToken> {
        let mut s = String::new(); self.next()?;
        let mut start = false;
        let mut trailing_space = false;
        loop {
            match self.curr {
                '\0' => return throw("unexpected quoted identifier"),
                '`' if start => return throw("empty quoted identifier"),
                '`' => return Ok(SToken::QuotedSymbol(s)),
                '\"' | '\n' | '\t' => return throw("invalid character in quoted identifier"),
                ' ' => { if !start {trailing_space = true}; s.push(' ') },
                c if start && c.is_digit(10) => return throw("quoted identifier can't start with digit"),
                _ if trailing_space => return throw("unexpected space inside of quoted symbol"),
                c => { start = false; s.push(c) },
            }
            self.next()?;
        }
    }

    fn read_field_idx(&mut self) -> io::Result<SToken> {
        let mut num: u32 = 0;
        while let Some(m) = self.curr.to_digit(10) {
            num = num.checked_mul(10).and_then(|n| n.checked_add(m))
                .ok_or_else(|| invalid("field notation index too large"))?;
            self.next()?;
        }
        Ok(SToken::FieldNum(num))
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
    // TODO: this is really inefficient use of the API
    fn try_prefix(&mut self, cs: &str) -> Result<Token, TryPrefix> {
        println!("try {:?}", cs);
        let subtrie = self.token_table.0.get_raw_descendant(cs).ok_or(TryPrefix::Done)?;
        println!("trie {:?}", subtrie);
        subtrie.value().cloned().ok_or_else(||
            if subtrie.is_empty() {TryPrefix::Done} else {TryPrefix::Next})
    }

    fn read_key_cmd_id(&mut self) -> io::Result<SToken> {
        let mut cs = String::new();

        fn cs_to_name(cs: &str) -> Name {
            let mut n: Name = Rc::new(Name2::Anon);
            let mut part = String::new();
            let mut escaped = false;
            for c in cs.chars() {
                match c {
                    '«' => escaped = true,
                    '»' => escaped = false,
                    '.' if !escaped =>
                        n = Rc::new(Name2::Str(n, mem::replace(&mut part, String::new()))),
                    c => part.push(c)
                }
            }
            Rc::new(Name2::Str(n, part))
        }

        if self.allow_field_notation && self.curr == '.' {
            if self.next()?.is_digit(10) {return self.read_field_idx()}
            if is_id_first(self.curr) && self.curr != '_' {
                self.read_id_part(&mut cs)?;
                return Ok(SToken::FieldName(cs_to_name(&cs)))
            }
            cs.push('.');
        } else {
            while is_id_first(self.curr) {
                self.read_id_part(&mut cs)?;
                if self.curr != '.' {break}
                cs.push('.');
                self.next()?;
            }
        }
        let id_sz = cs.len();
        cs.push(self.curr);
        println!("{:?}", cs);
        let mut best = None;

        for n in 1..cs.len() {
            println!("{:?}", (&cs, n, &best));
            match self.try_prefix(&cs[0..n]) {
                Ok(tk) => best = Some((tk, n)),
                Err(TryPrefix::Next) => (),
                Err(TryPrefix::Done) => break
            }
        }
        while best.is_none() {
            cs.push(self.next()?);
            println!("{:?} <-", cs);
            match self.try_prefix(&cs) {
                Ok(tk) => best = Some((tk, cs.len())),
                Err(TryPrefix::Next) => (),
                Err(TryPrefix::Done) => break
            }
        }
        let (tk, n) = match best {
            None => (SToken::Identifier(cs_to_name(&cs[0..id_sz])), id_sz),
            Some((Token {tk, prec: None}, n)) => (SToken::CommandKeyword(tk), n),
            Some((Token {tk, prec: Some(prec)}, n)) => (SToken::Keyword(tk, prec), n)
        };
        if n == 0 {return throw("unexpected token")}
        for c in cs.split_at(n).1.chars().rev().skip(1) { self.pushback(c) }
        Ok(tk)
    }

    pub fn scan(&mut self) -> io::Result<SToken> {
        loop {
            match self.curr {
                '\0' => return Ok(SToken::Eof),
                ' ' | '\r' | '\t' | '\n' => (),
                '\"' => return self.read_string(),
                '`' if self.in_notation => return self.read_quoted_symbol(),
                c if c.is_digit(10) => return self.read_number(),
                _ => {
                    match self.read_key_cmd_id()? {
                        SToken::Keyword(s, prec) => match s.as_ref() {
                            "--" => self.read_line_comment()?,
                            "/-" => self.read_block_comment()?,
                            "/--" => return self.read_doc_block(false),
                            "/-!" => return self.read_doc_block(true),
                            "\'" => return self.read_char(),
                            _ => return Ok(SToken::Keyword(s, prec)) },
                        k => return Ok(k) }
                } }
            self.next()?;
        }
    }
}

impl<T: Iterator<Item = io::Result<char>>> Iterator for Scanner<T> {
    type Item = io::Result<SToken>;

    fn next(&mut self) -> Option<io::Result<SToken>> {
        if self.curr == '\0' {return None}
        match self.scan() {
            Err(err) => Some(Err(err)),
            Ok(SToken::Eof) => None,
            Ok(tk) => Some(Ok(tk))
        }
    }
}
