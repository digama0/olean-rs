use std::io;
use radix_trie::{Trie, TrieCommon};
use num::{Ratio, BigInt, BigRational};
use super::loader::Loader;
use super::types::{Modification, Token};

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
    ("(", MAX_PREC), (")", 0), ("_", MAX_PREC),
    ("[", MAX_PREC), ("#[", MAX_PREC), ("]", 0), ("⦃", MAX_PREC), ("⦄", 0), (".(", 0),
    ("(!", MAX_PREC), ("!)", 0),
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

struct Scanner<T: Iterator<Item = io::Result<char>>> {
    source: T,
    pushback: Option<char>,
    curr: char
}

enum SToken {
    Keyword,
    CommandKeyword,
    Identifier,
    Numeral(BigInt),
    Decimal(BigRational),
    String,
    Char,
    QuotedSymbol,
    DocBlock,
    ModDocBlock,
    FieldNum,
    FieldName,
    Eof
}

fn invalid(s: &str) -> io::Error { io::Error::new(io::ErrorKind::InvalidData, s) }
fn throw<A>(s: &str) -> io::Result<A> { Err(invalid(s)) }

impl<T: Iterator<Item = io::Result<char>>> Scanner<T> {
    fn next(&mut self) -> io::Result<char> {
        self.curr = if let Some(pb) = self.pushback {
            self.pushback = None; pb
        } else if let Some(ch) = self.source.next() {ch?}
        else {'\0'};
        Ok(self.curr)
    }

    fn pushback(&mut self, last: char) {
        self.pushback = Some(self.curr);
        self.curr = last;
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
                match denom { Some(q) => q *= 10, None => () };
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

    fn scan(&mut self) -> io::Result<SToken> {
        loop {
            match self.curr {
                '\0' => return Ok(SToken::Eof),
                ' ' => (), '\r' => (), '\t' => (), '\n' => (),
                c if c.is_digit(10) => return self.read_number(),
                _ => unimplemented!()
            }
            self.next()?;
        }
    }
}
