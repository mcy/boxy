// Copyright 2022 Miguel Young de la Sota
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # `boxy` - declarative box-drawing characters
//!
//! ![Crates.io](https://img.shields.io/crates/v/boxy)
//! ![docs.rs](https://img.shields.io/docsrs/boxy)
//!
//! [Box-drawing characters](https://en.wikipedia.org/wiki/Box-drawing_character)
//! are used extensively in text user interfaces software for drawing lines,
//! boxes, and other shapes. Unicode provides a large assortment of them in the
//! Box Drawing block (`U+2500` to `U+257F`).
//!
//! Unfortunately it can be quite irritating to construct code points in this
//! range, and generating graphics using box drawing characters can be tedious.
//! This is true even when explicit formulas exist for subsets of the block.
//!
//! This crate provides the relevant lookup tables and exposes a nice interface
//! for generating characters via the [`Char`] type. For example:
//!
//! ```
//! let corner = boxy::Char::upper_left(boxy::Weight::Doubled);
//! let side = boxy::Char::horizontal(boxy::Weight::Doubled);
//!
//! let bx = format!(
//!   "{}{}{}\n{}{}{}",
//!   corner, side, corner.rotate_cw(1),
//!   corner.rotate_cw(3), side, corner.rotate_cw(2),
//! );
//!
//! assert_eq!(bx, "
//! ╔═╗
//! ╚═╝
//! ".trim());
//! ```
//!
//! This crate is `no_std` and will never panic, making it ideal for your
//! a e s t h e t i c kernel panic messages.

#![no_std]
#![deny(missing_docs, unused, unsafe_code, warnings)]

use core::fmt;

/// A weight for a [`Char`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Weight {
  /// A "normal" weight: `─`
  Normal,
  /// A "heavy" weight: `━`
  Thick,
  /// A "doubled" weight: `═`
  Doubled,
}

/// A style for a [`Char`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Style {
  /// Em-dashed: `╎`.
  Em,
  /// En-dashed: `┆`.
  En,
  /// Dotted: `┊`.
  Dot,
  /// Curved corners: `╭`.
  Curved,
}

/// A general box-drawing character.
///
/// A character is defined by a choice of [`Weight`]s for each direction, as
/// well as an optional overall style. Missing weights will be interpreted as
/// "empty" and won't be rendered. Completely empty spaces are rendered as
/// `' '`, the ASCII space (`U+0020`).
///
/// Note that all configuration is *best effort*. Unicode does not provide the
/// full combination of all possible weights (such as several potential
/// combinations involving [`Weight::Doubled`]). The precise choice of fallback
/// is an implementation detail; it's probably best to stick to combinations
/// that Unicode provides code points for.
///
/// This type is generally meant to be used with [`fmt::Display`], which
/// converts it into a best guess of the appropriate Unicode code point and
/// formats it. [`Char::into_char()`] and [`Char::into_ascii()`] will produce
/// a `char` and an ASCII `u8` each.
///
/// In addition to direct construction via struct literal, various methods are
/// available for modifying an existing `Char`.
#[derive(Copy, Clone, Debug, Default)]
pub struct Char {
  /// The weight for the "up" direction.
  pub up: Option<Weight>,
  /// The weight for the "right" direction.
  pub right: Option<Weight>,
  /// The weight for the "left" direction.
  pub left: Option<Weight>,
  /// The weight for the "down" direction.
  pub down: Option<Weight>,

  /// An optional style.
  pub style: Option<Style>,

  /// If set, [`Char::into_char()`] will delegate to [`Char::into_ascii()`].
  ///
  /// This includes calls to the [`fmt::Display`] and [`Into<char>`] impls.
  pub ascii: bool,
}

impl fmt::Display for Char {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(&self.into_char(), f)
  }
}

impl From<Char> for char {
  fn from(c: Char) -> char {
    c.into_char()
  }
}

impl Char {
  /// Returns a new `Char` with no contents (i.e., a space).
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::empty().into_char(), ' ');
  /// ```
  pub fn empty() -> Self {
    Self::default()
  }

  /// Returns a new `Char` for a vertical line of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::vertical(Weight::Normal).into_char(), '│');
  /// ```
  pub fn vertical(w: Weight) -> Self {
    Self {
      up: Some(w),
      down: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for a vertical line of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::horizontal(Weight::Thick).into_char(), '━');
  /// ```
  pub fn horizontal(w: Weight) -> Self {
    Self {
      left: Some(w),
      right: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for a cross of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::cross(Weight::Doubled).into_char(), '╬');
  /// ```
  pub fn cross(w: Weight) -> Self {
    Self {
      left: Some(w),
      right: Some(w),
      up: Some(w),
      down: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for an upper-left corner of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::upper_left(Weight::Normal).into_char(), '┌');
  /// ```
  pub fn upper_left(w: Weight) -> Self {
    Self {
      down: Some(w),
      right: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for an upper-left corner of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::upper_right(Weight::Thick).into_char(), '┓');
  /// ```
  pub fn upper_right(w: Weight) -> Self {
    Self {
      down: Some(w),
      left: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for an upper-left corner of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::lower_left(Weight::Doubled).into_char(), '╚');
  /// ```
  pub fn lower_left(w: Weight) -> Self {
    Self {
      up: Some(w),
      right: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for an upper-left corner of the given weight.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::lower_right(Weight::Normal).into_char(), '┘');
  /// ```
  pub fn lower_right(w: Weight) -> Self {
    Self {
      up: Some(w),
      left: Some(w),
      ..Self::default()
    }
  }

  /// Returns a new `Char` for a "T" shape pointing up.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::up_tee(Weight::Normal).into_char(), '┴');
  /// ```
  pub fn up_tee(w: Weight) -> Self {
    Self::cross(w).down(None)
  }

  /// Returns a new `Char` for a "T" shape pointing right.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::right_tee(Weight::Doubled).into_char(), '╠');
  /// ```
  pub fn right_tee(w: Weight) -> Self {
    Self::cross(w).left(None)
  }

  /// Returns a new `Char` for a "T" shape pointing left.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::left_tee(Weight::Thick).into_char(), '┫');
  /// ```
  pub fn left_tee(w: Weight) -> Self {
    Self::cross(w).right(None)
  }

  /// Returns a new `Char` for a "T" shape pointing down.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::down_tee(Weight::Normal).into_char(), '┬');
  /// ```
  pub fn down_tee(w: Weight) -> Self {
    Self::cross(w).up(None)
  }

  /// Returns a new `Char` for a half-line shape pointing up.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::up_half(Weight::Normal).into_char(), '╵');
  /// ```
  pub fn up_half(w: Weight) -> Self {
    Self::empty().up(w)
  }

  /// Returns a new `Char` for a half-line shape pointing up.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::right_half(Weight::Thick).into_char(), '╺');
  /// ```
  pub fn right_half(w: Weight) -> Self {
    Self::empty().right(w)
  }

  /// Returns a new `Char` for a half-line shape pointing up.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::left_half(Weight::Doubled).into_char(), '╸');
  /// ```
  pub fn left_half(w: Weight) -> Self {
    Self::empty().left(w)
  }

  /// Returns a new `Char` for a half-line shape pointing up.
  ///
  /// ```
  /// # use boxy::*;
  /// assert_eq!(Char::down_half(Weight::Normal).into_char(), '╷');
  /// ```
  pub fn down_half(w: Weight) -> Self {
    Self::empty().down(w)
  }

  /// Returns a copy with the given [`Weight`] for the "up" direction.
  ///  
  /// ```
  /// # use boxy::*;
  /// let c = Char::cross(Weight::Normal);
  /// assert_eq!(c.up(Weight::Thick).into_char(), '╀');
  /// ```
  pub fn up(self, w: impl Into<Option<Weight>>) -> Self {
    Self {
      up: w.into(),
      ..self
    }
  }

  /// Returns a copy with the given [`Weight`] for the "right" direction.
  ///  
  /// ```
  /// # use boxy::*;
  /// let c = Char::cross(Weight::Normal);
  /// assert_eq!(c.right(Weight::Thick).into_char(), '┾');
  /// ```
  pub fn right(self, w: impl Into<Option<Weight>>) -> Self {
    Self {
      right: w.into(),
      ..self
    }
  }

  /// Returns a copy with the given [`Weight`] for the "left" direction.
  ///  
  /// ```
  /// # use boxy::*;
  /// let c = Char::cross(Weight::Normal);
  /// assert_eq!(c.left(Weight::Thick).into_char(), '┽');
  /// ```
  pub fn left(self, w: impl Into<Option<Weight>>) -> Self {
    Self {
      left: w.into(),
      ..self
    }
  }

  /// Returns a copy with the given [`Weight`] for the "down" direction.
  ///  
  /// ```
  /// # use boxy::*;
  /// let c = Char::cross(Weight::Normal);
  /// assert_eq!(c.down(Weight::Thick).into_char(), '╁');
  /// ```
  pub fn down(self, w: impl Into<Option<Weight>>) -> Self {
    Self {
      down: w.into(),
      ..self
    }
  }

  /// Returns a copy with the given [`Style`].
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick);
  /// assert_eq!(c.into_char(), '┃');
  /// assert_eq!(c.style(Style::En).into_char(), '┇');
  /// ```
  pub fn style(self, s: impl Into<Option<Style>>) -> Self {
    Self {
      style: s.into(),
      ..self
    }
  }

  /// Returns a copy that's in ASCII mode.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick);
  /// assert_eq!(c.into_char(), '┃');
  /// assert_eq!(c.ascii().into_char(), '|');
  /// ```
  pub fn ascii(self) -> Self {
    Self {
      ascii: true,
      ..self
    }
  }

  /// Returns a copy with all present [`Weight`]s to `w`.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick).left(Weight::Normal);
  /// assert_eq!(c.into_char(), '┨');
  /// assert_eq!(c.weight(Weight::Doubled).into_char(), '╣');
  /// ```
  #[inline]
  pub fn weight(mut self, w: Weight) -> Self {
    for w2 in self.weights().into_iter().flatten() {
      *w2 = w;
    }
    self
  }

  /// Returns a copy where every empty direction is filled with the given
  /// [`Weight`].
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick);
  /// assert_eq!(c.into_char(), '┃');
  /// assert_eq!(c.fill(Weight::Normal).into_char(), '╂');
  /// ```
  #[inline]
  pub fn fill(self, w: Weight) -> Self {
    self.fill_from(Self::cross(w))
  }

  /// Replaces all directions that have `from` as their [`Weight`] with `to`.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick).left(Weight::Normal);
  /// assert_eq!(c.into_char(), '┨');
  /// assert_eq!(c.replace(Weight::Thick, None).into_char(), '╴');
  /// ```
  #[inline]
  pub fn replace(
    mut self,
    from: impl Into<Option<Weight>>,
    to: impl Into<Option<Weight>>,
  ) -> Self {
    let from = from.into();
    let to = to.into();

    for w in self.weights() {
      if *w == from {
        *w = to
      }
    }
    self
  }

  /// Returns a copy where every empty direction is replaced with a copy from
  /// `that`.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick);
  /// let fill = Char::cross(Weight::Normal);
  /// assert_eq!(c.into_char(), '┃');
  /// assert_eq!(c.fill_from(fill).into_char(), '╂');
  /// ```
  ///
  /// This function can be used to fill in possibly empty spaces from a
  /// template, overlaying `self` over `that`.
  ///
  /// Styles are not affected by this function.
  #[inline]
  pub fn fill_from(mut self, mut that: Self) -> Self {
    for (a, b) in
      Iterator::zip(self.weights().into_iter(), that.weights().into_iter())
    {
      *a = a.or(*b);
    }
    self
  }

  /// Returns a copy where every direction is cleared if it's empty in `that`.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char::vertical(Weight::Thick).fill(Weight::Normal);
  /// let stencil = Char::lower_left(Weight::Normal);
  /// assert_eq!(c.into_char(), '╂');
  /// assert_eq!(stencil.into_char(), '└');
  /// assert_eq!(c.crop_from(stencil).into_char(), '┖');
  /// ```
  ///
  /// This function can be used to make the shape of `self` fit inside that of
  /// `that`.
  ///
  /// Styles are not affected by this function.
  #[inline]
  pub fn crop_from(mut self, mut that: Self) -> Self {
    for (a, b) in
      Iterator::zip(self.weights().into_iter(), that.weights().into_iter())
    {
      *a = b.and(*a);
    }
    self
  }

  /// Returns a copy that's been rotated 90 degrees clockwise a number of times.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char {
  ///   left: Some(Weight::Normal), down: Some(Weight::Doubled),
  ///   ..Char::default()
  /// };
  /// assert_eq!(c.rotate_cw(0).into_char(), '╖');
  /// assert_eq!(c.rotate_cw(1).into_char(), '╛');
  /// assert_eq!(c.rotate_cw(2).into_char(), '╙');
  /// assert_eq!(c.rotate_cw(3).into_char(), '╒');
  /// ```
  #[inline]
  pub fn rotate_cw(mut self, turns: u32) -> Self {
    let mut new = self;
    let turns = turns as usize % 4;
    for i in 0..4 {
      *new.cw_weights()[(i + turns) % 4] = *self.cw_weights()[i];
    }
    new
  }

  /// Returns a copy that's been rotated 90 degrees counter-clockwise a number
  /// of times.
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char {
  ///   left: Some(Weight::Normal), down: Some(Weight::Doubled),
  ///   ..Char::default()
  /// };
  /// assert_eq!(c.rotate_ccw(0).into_char(), '╖');
  /// assert_eq!(c.rotate_ccw(1).into_char(), '╒');
  /// assert_eq!(c.rotate_ccw(2).into_char(), '╙');
  /// assert_eq!(c.rotate_ccw(3).into_char(), '╛');
  /// ```
  pub fn rotate_ccw(self, turns: u32) -> Self {
    self.rotate_cw(4 - (turns % 4))
  }

  /// Returns a copy that's been flipped horizontally (left and right
  /// interchanged).
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char {
  ///   left: Some(Weight::Normal), down: Some(Weight::Doubled),
  ///   ..Char::default()
  /// };
  /// assert_eq!(c.into_char(), '╖');
  /// assert_eq!(c.hflip().into_char(), '╓');
  /// ```
  pub fn hflip(self) -> Self {
    Self {
      left: self.right,
      right: self.left,
      ..self
    }
  }

  /// Returns a copy that's been flipped vertically (up and down
  /// interchanged).
  ///
  /// ```
  /// # use boxy::*;
  /// let c = Char {
  ///   left: Some(Weight::Normal), down: Some(Weight::Doubled),
  ///   ..Char::default()
  /// };
  /// assert_eq!(c.into_char(), '╖');
  /// assert_eq!(c.vflip().into_char(), '╜');
  /// ```
  pub fn vflip(self) -> Self {
    Self {
      up: self.down,
      down: self.up,
      ..self
    }
  }

  /// Approximates the description given by this `Char` as a Unicode code point.
  pub fn into_char(mut self) -> char {
    if self.ascii {
      return self.into_ascii() as char;
    }

    // If `has_thick`, we ignore all doubled weights, since Unicode
    // doesn't provide versions with both.
    let has_thick = self
      .weights()
      .iter()
      .any(|w| matches!(w, Some(Weight::Thick)));

    // Converts a weight into the appropriate index type for one of the lookup
    // tables.
    fn w2i(w: Option<Weight>) -> usize {
      match w {
        None => 0,
        Some(Weight::Normal) => 1,
        Some(Weight::Thick | Weight::Doubled) => 2,
      }
    }

    let lut = if has_thick { &LUT_THICK } else { &LUT_DOUBLED };
    let c = lut[w2i(self.down)][w2i(self.left)][w2i(self.right)][w2i(self.up)];

    // Manually convert any characters specifically affected by style. Note that
    // non-"normal" corners and doubled lines are intentionally NOT affected.
    match (c, self.style) {
      ('─', Some(Style::Em)) => '╌',
      ('─', Some(Style::En)) => '┄',
      ('─', Some(Style::Dot)) => '┈',
      ('━', Some(Style::Em)) => '╍',
      ('━', Some(Style::En)) => '┅',
      ('━', Some(Style::Dot)) => '┉',

      ('│', Some(Style::Em)) => '╎',
      ('│', Some(Style::En)) => '┆',
      ('│', Some(Style::Dot)) => '┊',
      ('┃', Some(Style::Em)) => '╏',
      ('┃', Some(Style::En)) => '┇',
      ('┃', Some(Style::Dot)) => '┋',

      ('┌', Some(Style::Curved)) => '╭',
      ('┐', Some(Style::Curved)) => '╮',
      ('┘', Some(Style::Curved)) => '╯',
      ('└', Some(Style::Curved)) => '╰',

      (c, _) => c,
    }
  }

  /// Approximates the description given by this `Char` as an ASCII byte.
  ///
  /// "ASCII fallback": if set, the produced code points will be some kind of
  /// clever fallback in the ASCII block. If `style` is `None`, it will be a
  /// combination of `|`, `-`, and `+`; other styles may use other ASCII
  /// characters on a best-effort-looks-about-right basis.
  ///
  /// ```
  /// let corner = boxy::Char::upper_left(boxy::Weight::Doubled).ascii();
  /// let side = boxy::Char::horizontal(boxy::Weight::Doubled).ascii();
  ///
  /// let bx = format!(
  ///   "{}{}{}\n{}{}{}",
  ///   corner, side, corner.rotate_cw(1),
  ///   corner.rotate_cw(3), side, corner.rotate_cw(2),
  /// );
  ///
  /// assert_eq!(bx, "
  /// +-+
  /// +-+
  /// ".trim());
  ///
  /// let corner = corner.style(boxy::Style::Curved);
  ///
  /// let bx = format!(
  ///   "{}{}{}\n{}{}{}",
  ///   corner, side, corner.rotate_cw(1),
  ///   corner.rotate_cw(3), side, corner.rotate_cw(2),
  /// );
  ///
  /// // This represents *possible* output.
  /// assert_eq!(bx, "
  /// .-.
  /// '-'
  /// ".trim());
  /// ```
  ///
  /// Compare with the example in the [module documentation][self].
  #[rustfmt::skip]
  pub fn into_ascii(self) -> u8 {
    match self {
      Self {
        up: None, left: None, right: None, down: None,
        ..
      } => b' ',

      Self {
        left: None, right: None,
        style: Some(Style::Em | Style::En | Style::Dot),
        ..
      } => b':',
      Self {
        left: None, right: None,
        ..
      } => b'|',

      Self {
        up: None, down: None,
        ..
      } => b'-',

      Self {
        up: None, right: None,
        style: Some(Style::Curved),
        ..
      } => b'.',
      Self {
        up: None, left: None,
        style: Some(Style::Curved),
        ..
      } => b'.',

      Self {
        down: None, right: None,
        style: Some(Style::Curved),
        ..
      } => b'\'',
      Self {
        down: None, left: None,
        style: Some(Style::Curved),
        ..
      } => b'\'',

      _ => b'+',
    }
  }

  /// Returns an array of references to each weight in declaration order.
  fn weights(&mut self) -> [&mut Option<Weight>; 4] {
    // Order is important: it's the field declaration order.
    [
      &mut self.up,
      &mut self.right,
      &mut self.left,
      &mut self.down,
    ]
  }

  /// Returns an array of references to each weight in clockwise order
  fn cw_weights(&mut self) -> [&mut Option<Weight>; 4] {
    // Order is important: it's the field declaration order.
    [
      &mut self.up,
      &mut self.right,
      &mut self.down,
      &mut self.left,
    ]
  }
}

// These tables are carefully constructed such that we can index them with each
// (possibly empty) direction in a specific order. Each bar can be either empty,
// normal, or "special"; the choice of the special weight is either thick or
// doubled, which covers the entirety of the range Unicode provides for us.
//
// The index order is the reverse of the field declaration order in the
// `Char` struct.

#[rustfmt::skip]
const LUT_THICK: [[[[char; 3]; 3]; 3]; 3] = [
  [
    [[' ', '╵', '╹'], ['╶', '└', '┖'], ['╺', '┕', '┗']],
    [['╴', '┘', '┚'], ['─', '┴', '┸'], ['╼', '┶', '┺']],
    [['╸', '┙', '┛'], ['╾', '┵', '┹'], ['━', '┷', '┻']],
  ],
  [
    [['╷', '│', '╿'], ['┌', '├', '┞'], ['┍', '┝', '┡']],
    [['┐', '┤', '┦'], ['┬', '┼', '╀'], ['┮', '┾', '╄']],
    [['┑', '┥', '┩'], ['┭', '┽', '╃'], ['┯', '┿', '╇']],
  ],
  [
    [['╻', '╽', '┃'], ['┎', '┟', '┠'], ['┏', '┢', '┣']],
    [['┒', '┧', '┨'], ['┰', '╁', '╂'], ['┲', '╆', '╊']],
    [['┓', '┪', '┫'], ['┱', '╅', '╉'], ['┳', '╈', '╋']],
  ],
];

#[rustfmt::skip]
const LUT_DOUBLED: [[[[char; 3]; 3]; 3]; 3] = [
  [
    [[' ', '╵', '║'], ['╶', '└', '╙'], ['═', '╘', '╚']],
    [['╴', '┘', '╜'], ['─', '┴', '╨'], ['═', '╧', '╩']],
    [['╸', '╛', '╝'], ['═', '╧', '╩'], ['═', '╧', '╩']],
  ],
  [
    [['╷', '│', '║'], ['┌', '├', '╟'], ['╒', '╞', '╠']],
    [['┐', '┤', '╢'], ['┬', '┼', '╫'], ['╤', '╪', '╬']],
    [['╕', '╡', '╣'], ['╤', '╪', '╬'], ['╤', '╪', '╬']],
  ],
  [
    [['║', '║', '║'], ['╓', '╟', '╟'], ['╔', '╠', '╠']],
    [['╖', '╢', '╢'], ['╥', '╫', '╫'], ['╦', '╬', '╬']],
    [['╗', '╣', '╣'], ['╦', '╬', '╬'], ['╦', '╬', '╬']],
  ],
];

// Note: the entirety of this crate's tests reside in its comments, which is
// why you don't see any tests here. :D
