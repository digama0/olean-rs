use std::io;
use std::mem;
use std::fmt;
use std::ops::Deref;
use crate::lexer::{Lexer, Token};
use crate::lexer::Token::*;
use crate::loader::Loader;
use crate::leanpath::LeanPath;
use crate::types::*;

fn invalid(s: &str) -> io::Error { io::Error::new(io::ErrorKind::InvalidData, s) }
fn throw<A>(s: &str) -> io::Result<A> { Err(invalid(s)) }
fn guard(b: bool, s: &str) -> io::Result<()> { if b {Ok(())} else {throw(s)} }

#[derive(Debug)] pub struct Attributes;
#[derive(Debug)] pub struct Modifiers;

#[derive(Debug)] pub struct CmdMeta {
    pub attr: Attributes,
    pub mods: Modifiers,
    pub doc: Option<String>
}

impl CmdMeta {
    fn new(doc: Option<String>) -> CmdMeta {
        CmdMeta {attr: Attributes, mods: Modifiers, doc}
    }

    fn check_empty(&self) -> io::Result<()> {
        guard(true, "command does not take attributes")?;
        guard(true, "command does not take modifiers")?;
        guard(self.doc.is_none(), "command does not take doc string")
    }
}

#[derive(Debug)] pub enum Command {
    Namespace(Name, Vec<Command>),
    Section(Option<Name>, Vec<Command>),
    Other(String, CmdMeta, Vec<Token>)
}

impl Command {
    pub fn write(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        match self {
            Command::Namespace(n, cmds) => {
                writeln!(f, "{:indent$}namespace {}", "", n, indent=depth)?;
                Command::write_vec(cmds, f, depth+2)
            },
            Command::Section(None, cmds) => {
                writeln!(f, "{:indent$}section", "", indent=depth)?;
                Command::write_vec(cmds, f, depth+2)
            },
            Command::Section(Some(n), cmds) => {
                writeln!(f, "{:indent$}section {}", "", n, indent=depth)?;
                Command::write_vec(cmds, f, depth+2)
            },
            Command::Other(s, _, _) => writeln!(f, "{:indent$}{} [...]", "", s, indent=depth)
        }
    }

    pub fn write_vec(cmds: &Vec<Command>, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        Ok(for cmd in cmds { cmd.write(f, depth)? })
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.write(f, 0) }
}

#[derive(PartialEq, Debug)] enum CmdEnd {
    End(Option<Name>),
    Eof
}

#[derive(Debug)] pub struct RoughLean {
    pub name: Name,
    pub imports: Vec<ModuleName>,
    pub doc: Vec<String>,
    pub cmds: Vec<Command>
}

impl RoughLean {
    fn new(name: Name, imports: Vec<ModuleName>) -> RoughLean {
        RoughLean { name, imports, doc: Vec::new(), cmds: Vec::new() }
    }
}

pub struct RoughParser<T: io::Read> {
    lexer: Lexer<T>,
    back: Option<Token>,
    mdoc: Vec<String>
}

impl<T: io::Read> RoughParser<T> {
    pub fn new(lexer: Lexer<T>) -> Self {
        RoughParser {lexer, back: None, mdoc: Vec::new()}
    }

    fn get(&mut self) -> io::Result<Token> {
        Ok(match self.back.take() {
            Some(tk) => tk,
            None => self.lexer.lex()?
        })
    }

    fn load(&mut self) -> io::Result<&Token> {
        if self.back.is_none() {
            self.back = Some(self.lexer.lex()?)
        }
        Ok(&self.back.as_ref().unwrap())
    }

    fn pushback(&mut self, tk: Token) { self.back = Some(tk) }

    fn lex_ident(&mut self) -> io::Result<Option<Name>> {
        Ok(match self.get()? {
            Identifier(s) => Some(s),
            tk => {self.pushback(tk); None}
        })
    }

    fn lex_tk(&mut self, s: &str) -> io::Result<bool> {
        let tk = self.get()?;
        if tk.is_tk(s) { Ok(true) } else { self.pushback(tk); Ok(false) }
    }

    pub fn parse_imports(&mut self) -> io::Result<Vec<ModuleName>> {
        let old = self.lexer.allow_field_notation(false);
        let mut imports = Vec::new();
        if !self.lex_tk("prelude")? {
            imports.push(ModuleName{name: name!(init), relative: None})
        }
        while self.lex_tk("import")? {
            loop {
                let mut relative: Option<u32> = None;
                loop {
                    let d = if let Some(s) = self.load()?.tk() {
                        if s.bytes().all(|c| c == ('.' as u8)) { s.len() as u32 }
                        else {break}
                    } else {break};
                    self.back = None;
                    if let Some(k) = &mut relative { *k += d }
                    else { relative = Some(d-1) }
                }
                if let Some(name) = self.lex_ident()? {
                    imports.push(ModuleName {name, relative})
                } else {break}
            }
        }
        self.lexer.allow_field_notation(old);
        Ok(imports)
    }

    fn parse_cmd(&mut self, meta: CmdMeta, s: String) -> io::Result<Command> {
        match s.deref() {
            "namespace" => { meta.check_empty()?; match self.lex_ident()? {
                Some(ns) => Ok(Command::Namespace(ns.clone(), self.parse_cmds(CmdEnd::End(Some(ns)))?)),
                None => throw("invalid namespace declaration, identifier expected")
            } },
            "section" => {
                meta.check_empty()?;
                let n = self.lex_ident()?;
                Ok(Command::Section(n.clone(), self.parse_cmds(CmdEnd::End(n))?))
            },
            _ => {
                let mut tks = Vec::new();
                let mut begins: u32 = 1;
                loop {
                    match self.get()? {
                        Token::Eof => break,
                        Token::Keyword(s, prec) => {
                            if s == "begin" || s == "match" {begins += 1}
                            tks.push(Token::Keyword(s, prec)) },
                        Token::CommandKeyword(s) =>
                            if if s == "end" {begins -= 1; begins == 0} else {true} {
                                self.pushback(Token::CommandKeyword(s)); break
                            } else {tks.push(Token::CommandKeyword(s))},
                        tk => tks.push(tk)
                    }
                }
                Ok(Command::Other(s, meta, tks))
            }
        }
    }

    fn parse_cmds(&mut self, expect: CmdEnd) -> io::Result<Vec<Command>> {
        let mut cmds = Vec::new();
        loop {
            match self.get()? {
                CommandKeyword(s) =>
                    if s == "end" {
                        return match &expect {
                            CmdEnd::Eof => throw("unexpected 'end'"),
                            CmdEnd::End(None) => Ok(cmds),
                            CmdEnd::End(Some(n)) =>
                                if self.lex_ident()? == Some(n.clone()) {Ok(cmds)}
                                else {throw(&format!("expected 'end {}'", n))}
                        }
                    } else { cmds.push(self.parse_cmd(CmdMeta::new(None), s)?) },
                DocBlock(true, s) => self.mdoc.push(s),
                DocBlock(false, s) =>
                    if let CommandKeyword(cmd) = self.get()? {
                        cmds.push(self.parse_cmd(CmdMeta::new(Some(s)), cmd)?)
                    } else { return throw("command expected") }
                Eof => return if expect == CmdEnd::Eof { Ok(cmds) } else { throw("unclosed namespace/section") },
                _ => return throw("command expected")
            }
        }
    }

    pub fn parse_lean(&mut self, load: &mut Loader, lp: &LeanPath, name: Name) -> io::Result<RoughLean> {
        let mut rl = RoughLean::new(name.clone(), self.parse_imports()?);
        for m in &rl.imports { load.load(lp, m.resolve(name.clone()))? }
        self.lexer.token_table.load(load)?;
        rl.cmds = self.parse_cmds(CmdEnd::Eof)?;
        rl.doc = mem::replace(&mut self.mdoc, Vec::new());
        Ok(rl)
    }
}
