#![no_std]
#![forbid(unsafe_code)]
#![warn(missing_docs)]
//! Pretty printer for non-overlapping code spans.
//!
//! This crate aids you in creating output like the following,
//! both for the terminal (ANSI) as well as for the web (HTML):
//!
//! <style>
//! pre span.red   { color: #dc322f; }
//! pre span.green { color: #859900; }
//! pre span.blue  { color: #268bd2; }
//! </style>
//! <pre style="background-color:#002b36; color:#93a1a1; line-height:1.0; font-size:x-large;">
//!   ╭─<span class=red>[main.rs]</span>
//!   │
//! 1 │ if true { 42 } else { "42" }
//!   ┆         <span class=green>───</span><span class=green>┬</span><span class=green>──</span>      <span class=blue>────</span><span class=blue>┬</span><span class=blue>───</span>
//!   ┆            <span class=green>│</span>            <span class=blue>│</span>
//!   ┆            <span class=green>╰</span><span class=green>─────────────────</span> this is of type Nat
//!   ┆                         <span class=blue>│</span>
//!   ┆                         <span class=blue>╰</span><span class=blue>────</span> this is of type String
//! ──╯
//! </pre>
//!
//! # Usage
//!
//! Suppose that we have a source file and a list of byte ranges that we want to annotate.
//! For example:
//!
//! ~~~
//! let src = r#"if true { 42 } else { "42" }"#;
//! let labels = [
//!     (8..14, "this is of type Nat"),
//!     (20..28, "this is of type String"),
//! ];
//! ~~~
//!
//! First, we have to create a [`LineIndex`].
//! This splits the source into lines, so that further functions can
//! quickly find in which line a byte is situated.
//!
//! ~~~
//! use codesnake::LineIndex;
//! # let src = r#"if true { 42 } else { "42" }"#;
//! let idx = LineIndex::new(src);
//! ~~~
//!
//! Next, we create a code [`Block`] from our index and the [`Label`]s:
//!
//! ~~~
//! use codesnake::{Block, Label};
//! # use codesnake::LineIndex;
//! # let src = r#"if true { 42 } else { "42" }"#;
//! # let idx = LineIndex::new(src);
//! # let labels = [(8..14, "this is of type Nat")];
//! let block = Block::new(&idx, labels.map(|(range, text)| Label::new(range, text))).unwrap();
//! ~~~
//!
//! This will fail if your labels refer to bytes outside the range of your source.
//!
//! Finally, we can print our code block:
//!
//! ~~~
//! # use codesnake::{Block, Label};
//! # use codesnake::LineIndex;
//! # let src = r#"if true { 42 } else { "42" }"#;
//! # let idx = LineIndex::new(src);
//! # let labels = [(8..14, "this is of type Nat")];
//! # let block = Block::new(&idx, labels.map(|(range, text)| Label::new(range, text))).unwrap();
//! // yield "  ╭─[main.rs]"
//! println!("{}{}", block.prologue(), "[main.rs]");
//! print!("{block}");
//! // yield "──╯"
//! println!("{}", block.epilogue());
//! ~~~
//!
//! # Colors
//!
//! To color the output on a terminal, you can use a crate like [`yansi`](https://docs.rs/yansi).
//! This allows you to color the snakes of a label as follows:
//!
//! ~~~
//! use codesnake::{Label, Snake};
//! use yansi::Paint;
//! # let (range, text) = (8..14, "this is of type Nat");
//! let label = Label::new(range, text).with_style(|s: &Snake| s.red().to_string());
//! ~~~
//!
//! For HTML, you can use something like:
//!
//! ~~~
//! use codesnake::{Label, Snake};
//! # let (range, text) = (8..14, "this is of type Nat");
//! let label = Label::new(range, text).with_style(|s: &Snake| {
//!     format!("<span style=\"color:red\">{s}</span>")
//! });
//! ~~~

extern crate alloc;

use alloc::string::{String, ToString};
use alloc::{boxed::Box, vec::Vec};
use core::fmt::{self, Display, Formatter};
use core::ops::Range;

/// Associate byte offsets with line numbers.
pub struct LineIndex<'a>(Vec<(usize, &'a str)>);

impl<'a> LineIndex<'a> {
    /// Create a new index.
    #[must_use]
    pub fn new(s: &'a str) -> Self {
        // indices of '\n' characters
        let newlines: Vec<_> = s
            .char_indices()
            .filter_map(|(i, c)| (c == '\n').then_some(i))
            .collect();
        // indices of line starts and ends
        let starts = core::iter::once(0).chain(newlines.iter().map(|i| *i + 1));
        let ends = newlines.iter().copied().chain(core::iter::once(s.len()));

        let lines = starts.zip(ends).map(|(start, end)| (start, &s[start..end]));
        Self(lines.collect())
    }

    fn get(&self, offset: usize) -> Option<IndexEntry> {
        use core::cmp::Ordering;
        let line_no = self.0.binary_search_by(|(line_start, line)| {
            if *line_start > offset {
                Ordering::Greater
            } else if line_start + line.len() < offset {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        });
        let line_no = line_no.ok()?;
        let (line_start, line) = self.0[line_no];
        Some(IndexEntry {
            line_no,
            line,
            bytes: offset - line_start,
        })
    }
}

#[derive(Debug)]
struct IndexEntry<'a> {
    line: &'a str,
    line_no: usize,
    bytes: usize,
}

/// Code label with text and style.
pub struct Label<T> {
    range: Range<usize>,
    text: T,
    style: Box<Style>,
}

type Style = dyn Fn(&Snake) -> String;

impl<T> Label<T> {
    /// Create a new label.
    ///
    /// If the range start equals the range end,
    /// an arrow is drawn at the range start.
    /// This can be useful to indicate errors that occur at the end of the input.
    #[must_use]
    pub fn new(range: Range<usize>, text: T) -> Self {
        Self {
            range,
            text,
            style: Box::new(Snake::to_string),
        }
    }
}

impl<T> Label<T> {
    /// Use a custom style for drawing the label's snake.
    #[must_use]
    pub fn with_style(self, style: impl Fn(&Snake) -> String + 'static) -> Self {
        Label {
            range: self.range,
            text: self.text,
            style: Box::new(style),
        }
    }
}

/// Sequence of numbered code lines with associated labels.
pub struct Block<C, T>(Vec<(usize, C, Labels<T>)>);

struct Labels<T> {
    incoming: Option<(usize, T)>,
    inside: Vec<Label<T>>,
    outgoing: Option<(usize, Box<Style>)>,
}

impl<T> Default for Labels<T> {
    fn default() -> Self {
        Self {
            incoming: None,
            inside: Vec::new(),
            outgoing: None,
        }
    }
}

impl<'a, T> Block<&'a str, T> {
    /// Create a new block.
    ///
    /// The label ranges `r` must fulfill the following conditions:
    ///
    /// * `r.start <= r.end`.
    /// * If the length of the string that was used to construct `idx` is `len`, then
    ///   `r.start <= len` and `r.end <= len`.
    /// * For any two subsequent labels with ranges `r1` and `r2`,
    ///   `r1.start < r2.start` and `r1.end <= r2.start`.
    ///
    /// If any of these conditions is not fulfilled, this function returns `None`.
    #[must_use]
    pub fn new(idx: &'a LineIndex, labels: impl IntoIterator<Item = Label<T>>) -> Option<Self> {
        let mut prev_range: Option<Range<_>> = None;
        let mut lines: Vec<(usize, &str, Labels<T>)> = Vec::new();
        for mut label in labels {
            if label.range.start > label.range.end {
                return None;
            }
            if let Some(prev) = prev_range.replace(label.range.clone()) {
                if label.range.start <= prev.start || label.range.start < prev.end {
                    return None;
                }
            }
            let start = idx.get(label.range.start)?;
            let end = idx.get(label.range.end)?;
            if lines.last().map_or(true, |last| last.0 != start.line_no) {
                lines.push((start.line_no, start.line, Labels::default()));
            }
            // this must always succeed, because if lines was empty initially,
            // then we pushed the current line to it
            let line = lines.last_mut()?;
            if end.line_no == line.0 {
                label.range = start.bytes..end.bytes;
                line.2.inside.push(label);
            } else {
                line.2.outgoing = Some((start.bytes, label.style));
                let next_labels = Labels {
                    incoming: Some((end.bytes, label.text)),
                    ..Default::default()
                };
                lines.push((end.line_no, end.line, next_labels));
            }
        }
        Some(Self(lines))
    }

    /// Apply function to code, then recalculate positions.
    #[must_use]
    pub fn map<C>(self, f: impl Fn(&str) -> C, width: impl Fn(&C) -> usize) -> Block<C, T> {
        let lines = self.0.into_iter().map(|(line_no, line, mut labels)| {
            labels.map_positions(|i| width(&f(&line[..i])));
            (line_no, f(line), labels)
        });
        Block(lines.collect())
    }
}

/// Line that precedes a block.
pub struct Prologue(usize);
/// Line that succeeds a block.
pub struct Epilogue(usize);

impl<C, T> Block<C, T> {
    /// Apply function to code without recalculating positions.
    #[must_use]
    pub fn map_code<C1>(self, f: impl Fn(C) -> C1) -> Block<C1, T> {
        let lines = self.0.into_iter();
        let lines = lines.map(|(line_no, line, labels)| (line_no, f(line), labels));
        Block(lines.collect())
    }

    fn some_incoming(&self) -> bool {
        self.0.iter().any(|(.., labels)| labels.incoming.is_some())
    }

    fn line_no_width(&self) -> usize {
        let max = self.0.last().unwrap().0 + 1;
        // number of digits; taken from https://stackoverflow.com/a/69302957
        core::iter::successors(Some(max), |&n| (n >= 10).then_some(n / 10)).count()
    }

    /// Return the line that precedes the block.
    #[must_use]
    pub fn prologue(&self) -> Prologue {
        Prologue(self.line_no_width())
    }

    /// Return the line that succeeds the block.
    #[must_use]
    pub fn epilogue(&self) -> Epilogue {
        Epilogue(self.line_no_width())
    }
}

impl Display for Prologue {
    /// " ... ╭─"
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{} {}{}",
            " ".repeat(self.0),
            Snake::UpRight,
            Snake::Horizontal(1)
        )
    }
}

impl Display for Epilogue {
    /// "─...─╯"
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", Snake::Horizontal(self.0 + 1), Snake::RightUp)
    }
}

impl<C: Display, T: Display> Display for Block<C, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let line_no_width = self.line_no_width();
        // " ...  │"
        writeln!(f, "{} {}", " ".repeat(line_no_width), Snake::Vertical)?;
        // " ...  ┆"
        let dots =
            |f: &mut Formatter| write!(f, "{} {}", " ".repeat(line_no_width), Snake::VerticalDots);
        let incoming_space =
            |f: &mut Formatter| write!(f, "{}", if self.some_incoming() { "  " } else { "" });
        let mut incoming_style: Option<&Style> = None;
        for (no, line, labels) in &self.0 {
            write!(f, "{:line_no_width$} │", no + 1)?;
            if let Some(style) = incoming_style {
                write!(f, " {}", style(&Snake::Vertical))?;
            } else {
                incoming_space(f)?;
            }
            writeln!(f, " {line}")?;

            dots(f)?;
            if let Some(style) = incoming_style {
                write!(f, " {}", style(&Snake::Vertical))?;
            } else {
                incoming_space(f)?;
            }
            labels.fmt_arrows(incoming_style, f)?;
            writeln!(f)?;

            if let Some(style) = incoming_style.take() {
                dots(f)?;
                write!(f, " ")?;
                labels.fmt_incoming(style, f)?;
                writeln!(f)?;
            }

            for i in 0..labels.inside.len() {
                dots(f)?;
                incoming_space(f)?;
                write!(f, " ")?;
                labels.fmt_inside_vert(i, f)?;
                writeln!(f)?;

                dots(f)?;
                incoming_space(f)?;
                write!(f, " ")?;
                labels.fmt_inside_text(i, f)?;
                writeln!(f)?;
            }

            if labels.outgoing.is_some() {
                dots(f)?;
                write!(f, " ")?;
                labels.fmt_outgoing(f)?;
                writeln!(f)?;
            }

            if let Some((_, style)) = &labels.outgoing {
                incoming_style = Some(style);
            }
        }
        Ok(())
    }
}

impl<T> Labels<T> {
    /// Position of the end of the rightmost label.
    fn width(&self) -> usize {
        let inside = self.inside.iter();
        inside
            .map(|Label { range, .. }| range.end + usize::from(range.start == range.end))
            .chain(self.incoming.iter().map(|(end, _)| *end))
            .chain(self.outgoing.iter().map(|(start, _)| *start + 1))
            .max()
            .unwrap()
    }

    fn map_positions(&mut self, f: impl Fn(usize) -> usize) {
        if let Some((end, _text)) = &mut self.incoming {
            *end = f(*end);
        }
        if let Some((start, _style)) = &mut self.outgoing {
            *start = f(*start);
        }
        for Label { range, .. } in &mut self.inside {
            *range = f(range.start)..f(range.end);
        }
    }
}

impl<T: Display> Labels<T> {
    /// Print something like "▲ ─┬─ ... ─┬─  ▲".
    fn fmt_arrows(&self, incoming: Option<&Style>, f: &mut Formatter) -> fmt::Result {
        let mut len = 0;
        if let Some(style) = incoming {
            let (end, _text) = self.incoming.as_ref().unwrap();
            write!(f, "{}{}", " ".repeat(*end), style(&Snake::ArrowUp))?;
            len = *end;
        } else {
            write!(f, " ")?;
        }

        for Label { range, style, .. } in &self.inside {
            write!(f, "{}", " ".repeat(range.start - len))?;
            if range.start == range.end {
                write!(f, "{}", style(&Snake::ArrowUp))?;
                len = range.end + 1;
            } else {
                let half_len = (range.end - range.start) / 2;
                write!(
                    f,
                    "{}{}{}",
                    style(&Snake::Horizontal(half_len)),
                    style(&Snake::HorizontalDown),
                    style(&Snake::Horizontal(range.end - (range.start + half_len + 1)))
                )?;
                len = range.end;
            }
        }

        if let Some((start, style)) = &self.outgoing {
            write!(f, "{}{}", " ".repeat(*start - len), style(&Snake::ArrowUp))?;
        }
        Ok(())
    }

    /// Print something like "╰─...─┴─...─ text".
    fn fmt_incoming(&self, style: &Style, f: &mut Formatter) -> fmt::Result {
        if let Some((end, text)) = &self.incoming {
            write!(
                f,
                "{}{}{}{} {}",
                style(&Snake::DownRight),
                style(&Snake::Horizontal(*end)),
                style(&Snake::HorizontalUp),
                style(&Snake::Horizontal(self.width() + 1 - end)),
                text
            )?;
        }
        Ok(())
    }

    /// Print something like "... │ ...  │"
    fn fmt_inside_vert(&self, i: usize, f: &mut Formatter) -> fmt::Result {
        let mut len = 0;
        for Label { range, .. } in &self.inside[..i] {
            write!(f, "{}", " ".repeat(range.end - len))?;
            len = range.end;
        }
        for Label { range, style, .. } in &self.inside[i..] {
            let mid = range.start + (range.end - range.start) / 2;
            write!(f, "{}{}", " ".repeat(mid - len), style(&Snake::Vertical))?;
            len = mid + 1;
        }
        if let Some((start, style)) = &self.outgoing {
            write!(f, "{}{}", " ".repeat(*start - len), style(&Snake::Vertical))?;
        }
        Ok(())
    }

    /// Print something like "╰─...─ text".
    fn fmt_inside_text(&self, i: usize, f: &mut Formatter) -> fmt::Result {
        let Label { range, text, style } = &self.inside[i];
        let mid = range.start + (range.end - range.start) / 2;
        write!(
            f,
            "{}{}{} {}",
            " ".repeat(mid),
            style(&Snake::DownRight),
            style(&Snake::Horizontal(self.width() - mid)),
            text
        )
    }

    /// Print something like "╭─...─╯".
    fn fmt_outgoing(&self, f: &mut Formatter) -> fmt::Result {
        if let Some((start, style)) = &self.outgoing {
            write!(
                f,
                "{}{}{}",
                style(&Snake::UpRight),
                style(&Snake::Horizontal(*start + 1)),
                style(&Snake::RightUp),
            )?;
        }
        Ok(())
    }
}

/// Parts used to draw code spans and lines.
#[derive(Copy, Clone)]
pub enum Snake {
    /// "─...─"
    Horizontal(usize),
    /// "│"
    Vertical,
    /// "┆"
    VerticalDots,
    /// "╭"
    UpRight,
    /// "╯"
    RightUp,
    /// "╰"
    DownRight,
    /// "▲"
    ArrowUp,
    /// "┴"
    HorizontalUp,
    /// "┬"
    HorizontalDown,
}

impl Display for Snake {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Horizontal(len) => "─".repeat(*len).fmt(f),
            Self::Vertical => "│".fmt(f),
            Self::VerticalDots => "┆".fmt(f),
            Self::UpRight => "╭".fmt(f),
            Self::RightUp => "╯".fmt(f),
            Self::DownRight => "╰".fmt(f),
            Self::ArrowUp => "▲".fmt(f),
            Self::HorizontalUp => "┴".fmt(f),
            Self::HorizontalDown => "┬".fmt(f),
        }
    }
}
