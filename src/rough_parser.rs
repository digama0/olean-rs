use std::io;
use std::mem;
use crate::tokens::TokenTable;
use crate::lexer::{Lexer, Token};
use crate::lexer::Token::*;
use crate::types::*;

pub struct RoughParser<T: io::Read> {
    lexer: Lexer<T>,
    curr: Token
}

#[derive(Debug)]
pub struct RoughLean {
    imports: Vec<ModuleName>
}
impl RoughLean {
    fn new() -> RoughLean {
        RoughLean { imports: Vec::new() }
    }
}
impl<T: io::Read> RoughParser<T> {
    pub fn new(mut lexer: Lexer<T>) -> io::Result<Self> {
        let curr = lexer.lex()?;
        Ok(RoughParser {lexer, curr})
    }

    fn lex(&mut self) -> io::Result<&Token> {
        self.curr = self.lexer.lex()?;
        Ok(&self.curr)
    }

    fn lex_ident(&mut self) -> io::Result<Option<Name>> {
        if let Identifier(s) = &mut self.curr {
            let new = mem::replace(s, name![DEAD]);
            self.lex()?;
            Ok(Some(new))
        } else { Ok(None) }
    }

    fn lex_tk(&mut self, s: &str) -> io::Result<bool> {
        if self.curr.is_tk(s) { self.lex()?; Ok(true) } else { Ok(false) }
    }

    fn parse_imports(&mut self) -> io::Result<Vec<ModuleName>> {
        let old = self.lexer.allow_field_notation(false);
        let mut imports = Vec::new();
        if !self.lex_tk("prelude")? {
            imports.push(ModuleName{name: name!(init), relative: None})
        }
        println!("hi {:?}", &self.curr);
        while self.lex_tk("import")? {
            println!("import");
            loop {
                println!("loop");
                let mut relative: Option<u32> = None;
                loop {
                    let d = if let Some(s) = self.curr.tk() {
                        if s.bytes().all(|c| c == ('.' as u8)) { s.len() as u32 }
                        else {break}
                    } else {break};
                    self.lex()?;
                    if let Some(k) = &mut relative { *k += d }
                    else { relative = Some(d-1) }
                }
                if let Some(name) = self.lex_ident()? {
                    println!("got {} {:?}", name, relative);
                    imports.push(ModuleName {name, relative})
                } else {break}
            }
        }
        self.lexer.allow_field_notation(old);
        Ok(imports)
    }

    pub fn parse(&mut self) -> io::Result<RoughLean> {
        let mut rl = RoughLean::new();
        rl.imports = self.parse_imports()?;
        Ok(rl)
    }
}
