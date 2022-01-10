# `boxy` - declarative box-drawing characters

[![Crates.io](https://img.shields.io/crates/v/boxy)](https://crates.io/crates/boxy)
[![docs.rs](https://img.shields.io/docsrs/boxy)](https://docs.rs/boxy/latest)

[Box-drawing characters](https://en.wikipedia.org/wiki/Box-drawing_character)
are used extensively in text user interfaces software for drawing lines,
boxes, and other shapes. Unicode provides a large assortment of them in the
Box Drawing block (`U+2500` to `U+257F`).

Unfortunately it can be quite irritating to construct code points in this
range, and generating graphics using box drawing characters can be tedious.
This is true even when explicit formulas exist for subsets of the block.

This crate provides the relevant lookup tables and exposes a nice interface
for generating characters via the `boxy::Char` type. For example:

```rust
let corner = boxy::Char::upper_left(boxy::Weight::Doubled);
let side = boxy::Char::horizontal(boxy::Weight::Doubled);

let bx = format!(
  "{}{}{}\n{}{}{}",
  corner, side, corner.rotate_cw(1),
  corner.rotate_cw(3), side, corner.rotate_cw(2),
);

assert_eq!(bx, "
╔═╗
╚═╝
".trim());
```

This crate is `no_std` and will never panic, making it ideal for your
a e s t h e t i c kernel panic messages.
