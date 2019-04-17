[![Build Status](https://travis-ci.org/cipher1024/olean-rs.svg?branch=master)](https://travis-ci.org/cipher1024/olean-rs)

# olean-rs
Parser/viewer for olean files, written in Rust and Lean.

See `olean.lean` for the lean version, and build with `cargo` for the Rust version. Currently the Rust version is faster by a factor of a hundred or so, so I don't know if I will continue to keep the Lean version up to speed.

Why look at olean files? The `olean` file format is an unstable binary format used by lean for caching successfully parsed files. As such, it is much easier to parse from a third party position than a `lean` file. Second, although lean supports an export format, the format is quite lossy, essentially only representing the expressions that are defined in the file. By contrast, the `olean` file contains lots of other information like notation declarations, attributes, `protected` status and namespace locations (which are not accessible through lean metaprogramming), and VM code. So `olean` parsing is the first step to a number of other processing or analysis passes.

## Building the Rust project

```shell
rustup toolchain install nightly
rustup override set nightly
cargo build
```

## Getting Started

```
Usage: target/debug/olean-rs [options]

Options:
    -D, --dump FILE     dump olean parse
    -d, --deps FILE     view all dependents of the target file
    -u, --unused FILE   list unused imports
    -L                  give location of lean library
    -p DIR              set current working directory
    -l lean.name        test lexer
    -t lean.name        testing
    -m, --makefile      generate a makefile to build project
    -h, --help          print this help menu
```
