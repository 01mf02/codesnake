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
//! use codesnake::CodeWidth;
//! # use codesnake::{Block, Label};
//! # use codesnake::LineIndex;
//! # let src = r#"if true { 42 } else { "42" }"#;
//! # let idx = LineIndex::new(src);
//! # let labels = [(8..14, "this is of type Nat")];
//! # let block = Block::new(&idx, labels.map(|(range, text)| Label::new(range, text))).unwrap();
//! let block = block.map_code(|c| CodeWidth::new(c, c.len()));
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
//! let label = Label::new(range, text).with_style(|s| s.red().to_string());
//! ~~~
//!
//! For HTML, you can use something like:
//!
//! ~~~
//! use codesnake::{Label, Snake};
//! # let (range, text) = (8..14, "this is of type Nat");
//! let label = Label::new(range, text).with_style(|s| {
//!     format!("<span style=\"color:red\">{s}</span>")
//! });
//! ~~~

extern crate alloc;

use alloc::string::{String, ToString};
use alloc::{boxed::Box, format, vec::Vec};
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
pub struct Label<C, T> {
    code: C,
    text: T,
    style: Box<Style>,
}

impl<T> Label<Range<usize>, T> {
    /// Create a new label.
    ///
    /// If the range start equals the range end,
    /// an arrow is drawn at the range start.
    /// This can be useful to indicate errors that occur at the end of the input.
    #[must_use]
    pub fn new(code: Range<usize>, text: T) -> Self {
        Self {
            code,
            text,
            style: Box::new(|s| s),
        }
    }
}

impl<C, T> Label<C, T> {
    /// Use a custom style for drawing the label's snake.
    #[must_use]
    pub fn with_style(self, style: impl Fn(String) -> String + 'static) -> Self {
        Self {
            code: self.code,
            text: self.text,
            style: Box::new(style),
        }
    }
}

/// Piece of code together with its display width.
pub struct CodeWidth<C> {
    code: C,
    width: usize,
}

impl<C> CodeWidth<C> {
    /// Create a new piece of code with associated display width.
    pub fn new(code: C, width: usize) -> Self {
        CodeWidth { code, width }
    }

    /// Width to the left and right of the center (excluding the center itself).
    fn left_right(&self) -> (usize, usize) {
        let left = self.width / 2;
        let right = self.width.checked_sub(left + 1).unwrap_or(0);
        (left, right)
    }
}

impl<C: Display> Display for CodeWidth<C> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.code.fmt(f)
    }
}

type Style = dyn Fn(String) -> String;

/// Sequence of numbered code lines with associated labels.
pub struct Block<C, T>(Vec<(usize, Parts<C, T>)>);

struct Parts<C, T> {
    incoming: Option<(C, T)>,
    inside: Vec<(C, Option<(T, Box<Style>)>)>,
    outgoing: Option<(C, Box<Style>)>,
}

impl<C, T> Default for Parts<C, T> {
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
    pub fn new<I>(idx: &'a LineIndex, labels: I) -> Option<Self>
    where
        I: IntoIterator<Item = Label<Range<usize>, T>>,
    {
        let mut prev_range: Option<Range<_>> = None;
        let mut lines: Vec<(usize, &str, Parts<Range<usize>, T>)> = Vec::new();
        for label in labels {
            if label.code.start > label.code.end {
                return None;
            }
            if let Some(prev) = prev_range.replace(label.code.clone()) {
                if label.code.start <= prev.start || label.code.start < prev.end {
                    return None;
                }
            }
            let start = idx.get(label.code.start)?;
            let end = idx.get(label.code.end)?;
            if lines.last().map_or(true, |last| last.0 != start.line_no) {
                lines.push((start.line_no, start.line, Parts::default()));
            }
            // this must always succeed, because if lines was empty initially,
            // then we pushed the current line to it
            let line = lines.last_mut()?;
            if end.line_no == line.0 {
                let label = (label.text, label.style);
                line.2.inside.push((start.bytes..end.bytes, Some(label)));
            } else {
                line.2.outgoing = Some((start.bytes..start.line.len(), label.style));
                let next_parts = Parts {
                    incoming: Some((0..end.bytes, label.text)),
                    ..Default::default()
                };
                lines.push((end.line_no, end.line, next_parts));
            }
        }

        let lines = lines.into_iter().map(|(line_no, line, parts)| {
            let len = line.len();
            let start = parts.incoming.as_ref().map_or(0, |(code, _)| code.end);
            let end = parts.outgoing.as_ref().map_or(len, |(code, _)| code.start);
            let last = parts.inside.last().map_or(start, |(code, _)| code.end);

            let incoming = parts.incoming.map(|(code, text)| (&line[..code.end], text));
            let outgoing = parts.outgoing.map(|(code, sty)| (&line[code.start..], sty));

            let mut pos = start;
            let unlabelled = |start, end| (start < end).then(|| (&line[start..end], None));
            let inside = parts.inside.into_iter().flat_map(|(code, label)| {
                let unlabelled = unlabelled(pos, code.start);
                let labelled = (&line[code.start..code.end], label);
                pos = code.end;
                unlabelled.into_iter().chain([labelled])
            });
            let parts = Parts {
                incoming,
                inside: inside.chain(unlabelled(last, end)).collect(),
                outgoing,
            };
            (line_no, parts)
        });

        Some(Self(lines.collect()))
    }
}

/// Line that precedes a block.
pub struct Prologue(usize);
/// Line that succeeds a block.
pub struct Epilogue(usize);

impl<C, T> Block<C, T> {
    /// Apply function to code.
    #[must_use]
    pub fn map_code<C1>(self, f: impl Fn(C) -> C1) -> Block<C1, T> {
        let lines = self.0.into_iter();
        Block(lines.map(|(no, parts)| (no, parts.map_code(&f))).collect())
    }

    fn some_incoming(&self) -> bool {
        self.0.iter().any(|(.., parts)| parts.incoming.is_some())
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
            Snake::Horizontal
        )
    }
}

impl Display for Epilogue {
    /// "─...─╯"
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", Snake::line_up(self.0 + 1))
    }
}

impl<C: Display, T: Display> Display for Block<CodeWidth<C>, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let line_no_width = self.line_no_width();
        // " ...  │"
        writeln!(f, "{} {}", " ".repeat(line_no_width), Snake::Vertical)?;
        // " ...  ┆"
        let dots =
            |f: &mut Formatter| write!(f, "{} {}", " ".repeat(line_no_width), Snake::VerticalDots);
        let incoming_space =
            |f: &mut Formatter| write!(f, "{}", if self.some_incoming() { "  " } else { "" });
        // the incoming style of the current line is the same as
        // the outgoing style of the previous line
        let mut incoming_style: Option<&Style> = None;
        for (line_no, parts) in &self.0 {
            write!(f, "{:line_no_width$} │", line_no + 1)?;
            if let Some(style) = incoming_style {
                write!(f, " {}", style(Snake::Vertical.to_string()))?;
            } else {
                incoming_space(f)?;
            }

            write!(f, " ")?;
            parts.fmt_code(incoming_style, f)?;
            writeln!(f)?;

            dots(f)?;
            write!(f, " ")?;
            if let Some(style) = incoming_style {
                style(Snake::Vertical.to_string()).fmt(f)?;
                parts.fmt_incoming(style, Snake::ArrowUp, f)?;
            } else {
                incoming_space(f)?;
            }
            parts.fmt_arrows(f)?;
            writeln!(f)?;

            if let (Some((code, text)), Some(style)) = (&parts.incoming, incoming_style) {
                dots(f)?;
                write!(f, " ")?;
                style(Snake::Vertical.to_string()).fmt(f)?;
                parts.fmt_incoming(style, Snake::Vertical, f)?;
                parts.fmt_inside_vert(0, f)?;
                writeln!(f)?;

                dots(f)?;
                write!(f, " ")?;
                let snake = Snake::down_line_up_line(code.width, parts.width() + 1 - code.width);
                write!(f, "{} {}", style(snake), text)?;
                writeln!(f)?;
            }

            let prefix = |f: &mut _| {
                dots(f)?;
                incoming_space(f)?;
                write!(f, " ")?;
                " ".repeat(parts.incoming.as_ref().map_or(0, |(code, _)| code.width))
                    .fmt(f)?;
                Ok(())
            };
            for i in 0..parts.inside.len() {
                if parts.inside[i].1.is_none() {
                    continue;
                }
                prefix(f)?;
                parts.fmt_inside_vert(i, f)?;
                writeln!(f)?;

                prefix(f)?;
                parts.fmt_inside_text(i, f)?;
                writeln!(f)?;
            }

            if let Some((_, style)) = &parts.outgoing {
                dots(f)?;
                write!(f, " ")?;
                style(Snake::up_line_up(parts.width())).fmt(f)?;
                writeln!(f)?;
            }
            incoming_style = parts.outgoing.as_ref().map(|(_code, style)| &**style);
        }
        Ok(())
    }
}

impl<C: Display, T> Parts<C, T> {
    fn fmt_code(&self, incoming: Option<&Style>, f: &mut Formatter) -> fmt::Result {
        if let (Some((code, _text)), Some(style)) = (&self.incoming, incoming) {
            write!(f, "{}", style(code.to_string()))?
        }

        for (code, label) in &self.inside {
            match label {
                Some((_text, style)) => write!(f, "{}", style(code.to_string()))?,
                None => write!(f, "{code}")?,
            }
        }
        if let Some((code, style)) = &self.outgoing {
            write!(f, "{}", style(code.to_string()))?
        }
        Ok(())
    }
}

impl<C, T> Parts<C, T> {
    #[must_use]
    fn map_code<C1>(self, f: impl Fn(C) -> C1) -> Parts<C1, T> {
        let inside = self.inside.into_iter();
        Parts {
            incoming: self.incoming.map(|(code, text)| (f(code), text)),
            inside: inside.map(|(code, label)| (f(code), label)).collect(),
            outgoing: self.outgoing.map(|(code, style)| (f(code), style)),
        }
    }
}

impl<C, T> Parts<CodeWidth<C>, T> {
    /// Position of the end of the rightmost label.
    fn width(&self) -> usize {
        let inside = self.inside.iter().map(|(code, _)| code.width);
        inside
            .chain(self.incoming.iter().map(|(code, _)| code.width))
            .chain(self.outgoing.iter().map(|(code, _)| code.width))
            .sum()
    }

    fn fmt_incoming(&self, style: &Style, snake: Snake, f: &mut Formatter) -> fmt::Result {
        if let Some((code, _text)) = &self.incoming {
            write!(f, "{}{}", " ".repeat(code.width), style(snake.to_string()))?;
        }
        Ok(())
    }

    fn fmt_inside<F>(&self, from: usize, snake: F, f: &mut Formatter) -> fmt::Result
    where
        F: Fn(usize, usize) -> String,
    {
        let before = self.inside[..from].iter().map(|(code, _)| code.width).sum();
        write!(f, "{}", " ".repeat(before))?;

        for (code, label) in &self.inside[from..] {
            if let Some((_text, style)) = label {
                let (left, right) = code.left_right();
                style(snake(left, right)).fmt(f)?;
            } else {
                " ".repeat(code.width).fmt(f)?;
            }
        }
        Ok(())
    }

    /// Print something like "... ─┬─ ... ─┬─ ... ▲".
    fn fmt_arrows(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_inside(0, Snake::line_down_line, f)?;

        if let Some((_code, style)) = &self.outgoing {
            style(Snake::ArrowUp.to_string()).fmt(f)?;
        }
        Ok(())
    }

    /// Print something like "... │ ...  │"
    fn fmt_inside_vert(&self, from: usize, f: &mut Formatter) -> fmt::Result {
        let snake = |l, r| format!("{}{}{}", " ".repeat(l), Snake::Vertical, " ".repeat(r));
        self.fmt_inside(from, snake, f)?;

        if let Some((_code, style)) = &self.outgoing {
            write!(f, "{}", style(Snake::Vertical.to_string()))?;
        }
        Ok(())
    }
}

impl<C, T: Display> Parts<CodeWidth<C>, T> {
    /// Print something like "╰─...─ text".
    fn fmt_inside_text(&self, i: usize, f: &mut Formatter) -> fmt::Result {
        let (before, then) = self.inside.split_at(i);
        let before: usize = before.iter().map(|(code, _)| code.width).sum();
        let after: usize = then[1..].iter().map(|(code, _)| code.width).sum();
        let outgoing = self.outgoing.as_ref().map_or(0, |(code, _)| code.width);
        let (code, label) = &self.inside[i];
        let (text, style) = label.as_ref().unwrap();
        let (left, right) = code.left_right();
        let snake = Snake::down_line(right + after + outgoing + 1);
        write!(f, "{}{} {}", " ".repeat(before + left), style(snake), text)
    }
}

/// Parts used to draw code spans and lines.
#[derive(Copy, Clone)]
pub enum Snake {
    /// "─"
    Horizontal,
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

impl Snake {
    /// ─...─
    fn line(len: usize) -> String {
        "─".repeat(len)
    }

    /// ╰─...─
    fn down_line(len: usize) -> String {
        format!("{}{}", Snake::DownRight, Snake::line(len))
    }

    /// ╰─...─┴─...─
    fn down_line_up_line(l: usize, r: usize) -> String {
        format!(
            "{}{}{}{}",
            Self::DownRight,
            Self::line(l),
            Self::HorizontalUp,
            Self::line(r)
        )
    }

    /// "╭─...─╯"
    fn up_line_up(len: usize) -> String {
        format!("{}{}{}", Self::UpRight, Self::line(len), Self::RightUp)
    }

    /// "─...─╯"
    fn line_up(len: usize) -> String {
        format!("{}{}", Self::line(len), Self::RightUp)
    }

    /// ─...─┬─...─
    fn line_down_line(l: usize, r: usize) -> String {
        format!("{}{}{}", Self::line(l), Self::HorizontalDown, Self::line(r))
    }
}

impl Display for Snake {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Horizontal => "─",
            Self::Vertical => "│",
            Self::VerticalDots => "┆",
            Self::UpRight => "╭",
            Self::RightUp => "╯",
            Self::DownRight => "╰",
            Self::ArrowUp => "▲",
            Self::HorizontalUp => "┴",
            Self::HorizontalDown => "┬",
        }
        .fmt(f)
    }
}
