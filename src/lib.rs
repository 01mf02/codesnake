#![no_std]
#![forbid(unsafe_code)]
#![warn(missing_docs)]
//! Pretty printer for non-overlapping code spans.
//!
//! This crate aids you in creating output like the following,
//! both for the terminal (ANSI) as well as for the web (HTML):
//!
//! <!-- colors taken from https://en.wikipedia.org/wiki/Solarized -->
//! <style>
//! pre span.red   { color: #dc322f; }
//! pre span.green { color: #859900; }
//! pre span.blue  { color: #268bd2; }
//! pre span.yellow{ color: #b58900; }
//! </style>
//! <pre style="background-color:#002b36; color:#93a1a1; line-height:1.0; font-size:large;">
//!   ╭─<span class=red>[fac.lisp]</span>
//!   │
//! 1 │   (defun <span class=green>factorial</span> (n) <span class=blue>(if (zerop n) 1</span>
//!   ┆          <span class=green>────┬────</span>     <span class=blue>▲</span>
//!   ┆          <span class=green>    │    </span>     <span class=blue>│</span>
//!   ┆              <span class=green>╰─────────────────────────</span> this function ...
//!   ┆ <span class=blue>╭──────────────────────╯</span>
//! 2 │ <span class=blue>│</span> <span class=blue>        (* n (factorial (1- n))))</span>)<span class=yellow></span>
//!   ┆ <span class=blue>│</span>                                 <span class=blue>▲</span> <span class=yellow>┬</span>
//!   ┆ <span class=blue>│</span>                                 <span class=blue>│</span> <span class=yellow>│</span>
//!   ┆ <span class=blue>╰─────────────────────────────────┴───</span> ... is defined by this
//!   ┆                                     <span class=yellow>│</span>
//!   ┆                                     <span class=yellow>╰─</span> (and here is EOF)
//! ──╯
//! </pre>
//!
//! This example has been created with `cargo run --example example -- --html`.
//! To see its console output, run `cargo run --example example`.
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
//! let block = Block::new(&idx, labels.map(|(range, text)| Label::<_, _, ()>::new(range).with_text(text))).unwrap();
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
//! # let block = Block::new(&idx, labels.map(|(range, text)| Label::<_, _, ()>::new(range).with_text(text))).unwrap();
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
//! use codesnake::Label;
//! use yansi::Paint;
//! # let (range, text) = (8..14, "this is of type Nat");
//! let label = Label::new(range).with_text(text).with_style(yansi::Color::Red);
//! ~~~
//!
//! For HTML, you can use something like:
//!
//! ~~~
//! use codesnake::Label;
//! # let (range, text) = (8..14, "this is of type Nat");
//! let label = Label::new(range).with_text(text).with_style("color:red");
//! ~~~

extern crate alloc;

use alloc::string::{String, ToString};
use alloc::{format, vec::Vec};
use core::fmt::{self, Display, Formatter};
use core::ops::Range;

/// Associate byte offsets with line numbers.
///
/// If `idx = LineIndex::new(s)` and `idx.0[n] = (offset, line)`, then
/// the `n`-th line of `s` starts at `offset` in `s` and equals `line`.
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

    fn get(&self, offset: usize) -> Option<IndexEntry<'_>> {
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

struct IndexEntry<'a> {
    line: &'a str,
    line_no: usize,
    /// offset of position relative to start of line
    bytes: usize,
}

enum LabelKind<T> {
    None,
    Snake,
    Text(T),
}

impl<T> LabelKind<T> {
    fn has_snake(&self) -> bool {
        match self {
            Self::None => false,
            Self::Snake | Self::Text(_) => true,
        }
    }

    fn text(self) -> Option<T> {
        match self {
            Self::None | Self::Snake => None,
            Self::Text(t) => Some(t),
        }
    }
}

/// Code label with text and style.
pub struct Label<C, T, S = ()> {
    code: C,
    kind: LabelKind<T>,
    style: S,
}

impl<T, S: Default> Label<Range<usize>, T, S> {
    /// Create a new label.
    ///
    /// If the range start equals the range end,
    /// an arrow is drawn at the range start.
    /// This can be useful to indicate errors that occur at the end of the input.
    #[must_use]
    pub fn new(code: Range<usize>) -> Self {
        Self {
            code,
            kind: LabelKind::Snake,
            style: S::default(),
        }
    }
}

impl<C, T, S> Label<C, T, S> {
    /// Provide text for the label.
    #[must_use]
    pub fn with_text(self, text: T) -> Self {
        let kind = LabelKind::Text(text);
        Self { kind, ..self }
    }

    /// Create an unmarked label (just the source line, no annotation)
    #[must_use]
    pub fn unmarked(self) -> Self {
        let kind = LabelKind::None;
        Self { kind, ..self }
    }

    /// Use a custom style for drawing the label's snake.
    #[must_use]
    pub fn with_style(self, style: S) -> Self {
        Self { style, ..self }
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
        let right = self.width.saturating_sub(left + 1);
        (left, right)
    }
}

impl<C: Display> Display for CodeWidth<C> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.code.fmt(f)
    }
}

type Paint<S> = fn(&mut Formatter, &S, &str) -> fmt::Result;

/// Sequence of lines, containing code `C`, (label) text `T`, and style `S`.
pub struct Block<C, T, S> {
    lines: Vec<Option<Line<C, T, S>>>,
    paint: Paint<S>,
}

struct Line<C, T, S> {
    no: usize,
    parts: LineParts<C, T, S>,
}

impl<C, T, S> Line<C, T, S> {
    fn map_code<C1>(self, f: impl FnMut(C) -> C1) -> Line<C1, T, S> {
        Line {
            no: self.no,
            parts: self.parts.map_code(f),
        }
    }
}

/// Line parts, containing code `C`, (label) text `T`, and style `S`.
struct LineParts<C, T, S> {
    /// snake that comes from another line, potentially with text
    incoming: Option<(C, Option<T>, S)>,
    inside: Vec<(C, LabelKind<T>, S)>,
    /// snake that starts on current line and extends to another line
    outgoing: Option<(C, S)>,
}

impl<C, T, S> LineParts<C, T, S> {
    fn arrows_below(&self) -> bool {
        let inside = |(_code, label, _style): &_| LabelKind::has_snake(label);
        self.incoming.is_some() || self.outgoing.is_some() || self.inside.iter().any(inside)
    }
}

impl<C, T, S> Default for LineParts<C, T, S> {
    fn default() -> Self {
        Self {
            incoming: None,
            inside: Vec::new(),
            outgoing: None,
        }
    }
}

impl<'a, T, S: Default + Clone> Block<&'a str, T, S> {
    /// Create a new block.
    ///
    /// Given a sequence of labels, find all input lines that are touched by the labels.
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
    pub fn new<I>(idx: &'a LineIndex, labels: I) -> Option<Self>
    where
        I: IntoIterator<Item = Label<Range<usize>, T, S>>,
    {
        let mut prev_range: Option<Range<_>> = None;
        let mut lines = Vec::new();
        for Label { kind, code, style } in labels {
            if code.start > code.end {
                return None;
            }
            if let Some(prev) = prev_range.replace(code.clone()) {
                if code.start <= prev.start || code.start < prev.end {
                    return None;
                }
            }
            let start = idx.get(code.start)?;
            let end = idx.get(code.end)?;
            debug_assert!(start.line_no <= end.line_no);

            let mut parts = match lines.pop() {
                Some(Some((line_no, _line, parts))) if line_no == start.line_no => parts,
                Some(line) => {
                    let non_consecutive = line
                        .as_ref()
                        .filter(|(no, ..)| start.line_no > no + 1)
                        .is_some();

                    lines.push(line);
                    if non_consecutive {
                        lines.push(None);
                    }
                    LineParts::default()
                }
                None => LineParts::default(),
            };

            if start.line_no == end.line_no {
                parts.inside.push((start.bytes..end.bytes, kind, style));
                lines.push(Some((start.line_no, start.line, parts)));
            } else {
                let range = start.bytes..start.line.len();
                if kind.has_snake() {
                    parts.outgoing = Some((range, style.clone()));
                } else {
                    parts.inside.push((range, LabelKind::None, style.clone()));
                }
                lines.push(Some((start.line_no, start.line, parts)));

                for line_no in start.line_no + 1..end.line_no {
                    let line = idx.0[line_no].1;
                    let parts = LineParts {
                        inside: Vec::from([(0..line.len(), LabelKind::None, style.clone())]),
                        ..Default::default()
                    };
                    lines.push(Some((line_no, line, parts)));
                }

                let mut parts = LineParts::default();
                let range = 0..end.bytes;
                if kind.has_snake() {
                    parts.incoming = Some((range, kind.text(), style.clone()));
                } else {
                    parts.inside.push((range, LabelKind::None, style.clone()));
                }
                lines.push(Some((end.line_no, end.line, parts)));
            }
        }

        let lines = lines.into_iter().map(|line| {
            line.map(|(no, line, parts)| Line {
                no,
                parts: parts.segment(line),
            })
        });
        Some(Block {
            lines: lines.collect(),
            paint: |f, _, s| write!(f, "{s}"),
        })
    }
}

/// Line that precedes a block.
pub struct Prologue(usize);
/// Line that succeeds a block.
pub struct Epilogue(usize);

impl<C, T, S> Block<C, T, S> {
    /// Apply function to code.
    #[must_use]
    pub fn map_code<C1>(self, mut f: impl FnMut(C) -> C1) -> Block<C1, T, S> {
        let f = |line: Option<Line<C, T, S>>| line.map(|line| line.map_code(&mut f));
        Block {
            lines: self.lines.into_iter().map(f).collect(),
            paint: self.paint,
        }
    }

    fn some_incoming(&self) -> bool {
        let mut lines = self.lines.iter().flatten();
        lines.any(|line| line.parts.incoming.is_some())
    }

    fn line_no_width(&self) -> usize {
        let max = self.lines.iter().flatten().next_back().unwrap().no + 1;
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

impl<C, T, S> Block<C, T, S> {
    /// Format styled code/snakes.
    ///
    /// By default, code/snakes are printed without considering their style.
    #[must_use]
    pub fn with_paint(self, paint: Paint<S>) -> Self {
        Self { paint, ..self }
    }

    /// " ...  ┆"
    fn dots(&self, f: &mut Formatter) -> fmt::Result {
        self.line_no_space_then(Snake::VerticalDots, f)
    }

    /// " ...  ?"
    fn line_no_space_then(&self, snake: Snake, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} {}", " ".repeat(self.line_no_width()), snake)
    }

    fn incoming_space(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", if self.some_incoming() { "  " } else { "" })
    }

    /// Write line number right-aligned.
    fn line_no(&self, no: usize, f: &mut Formatter) -> fmt::Result {
        let width = self.line_no_width();
        write!(f, "{:width$} │", no + 1)
    }
}

impl<C: Display, T: Display, S> Display for Block<CodeWidth<C>, T, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.line_no_space_then(Snake::Vertical, f)?;
        writeln!(f)?;

        let mut incoming_style: Option<&S> = None;

        for line in &self.lines {
            let Line { no: line_no, parts } = if let Some(line) = line {
                line
            } else {
                self.dots(f)?;
                writeln!(f)?;
                continue;
            };

            self.line_no(*line_no, f)?;
            if let Some(style) = incoming_style {
                write!(f, " ")?;
                (self.paint)(f, style, Snake::Vertical.as_str())?;
            } else {
                self.incoming_space(f)?;
            }

            write!(f, " ")?;
            for (code, style) in parts.code_parts() {
                (self.paint)(f, style, &code.to_string())?;
            }
            writeln!(f)?;

            // print the line just below the code, e.g.
            // " ...  ┆ │ ... ─┬─ ... ─┬─ ... ▲"
            if parts.arrows_below() {
                self.dots(f)?;
                write!(f, " ")?;
                if let Some(style) = incoming_style {
                    (self.paint)(f, style, Snake::Vertical.as_str())?;
                    parts.fmt_incoming(self.paint, style, Snake::ArrowUp, f)?;
                } else {
                    self.incoming_space(f)?;
                }
                parts.fmt_arrows(self.paint, f)?;
                writeln!(f)?;
            }

            if let Some((code, text, style)) = &parts.incoming {
                assert!(incoming_style.take().is_some());

                self.dots(f)?;
                write!(f, " ")?;
                (self.paint)(f, style, Snake::Vertical.as_str())?;
                parts.fmt_incoming(self.paint, style, Snake::Vertical, f)?;
                parts.fmt_inside_vert(self.paint, 0, f)?;
                writeln!(f)?;

                self.dots(f)?;
                write!(f, " ")?;
                if let Some(text) = text {
                    let snake =
                        Snake::down_line_up_line(code.width, parts.width() + 1 - code.width);
                    (self.paint)(f, style, &snake)?;
                    write!(f, " {text}")?;
                } else {
                    let snake = Snake::down_line_up(code.width);
                    (self.paint)(f, style, &snake)?;
                    parts.fmt_inside_vert(self.paint, 0, f)?;
                }
                writeln!(f)?;
            }

            let incoming_width = width2(&parts.incoming);
            let mut before = 0;
            let prefix = |f: &mut _| {
                self.dots(f)?;
                self.incoming_space(f)?;
                write!(f, " ")?;
                " ".repeat(incoming_width).fmt(f)?;
                Ok(())
            };
            for (i, (code, label, style)) in parts.inside.iter().enumerate() {
                if let LabelKind::Text(text) = label {
                    prefix(f)?;
                    // "... │ ... │"
                    parts.fmt_inside_vert(self.paint, i, f)?;
                    writeln!(f)?;

                    prefix(f)?;

                    // "╰─...─ {text}"
                    let (left, right) = code.left_right();
                    let after =
                        width2(&parts.inside) - before - code.width + width(&parts.outgoing);
                    let snake = Snake::down_line(right + after + 1);
                    write!(f, "{}", " ".repeat(before + left))?;
                    (self.paint)(f, style, &snake)?;
                    write!(f, " {text}")?;
                    writeln!(f)?;
                }
                before += code.width;
            }

            // " ...  ┆ ╭─...─╯"
            if let Some((_, style)) = &parts.outgoing {
                self.dots(f)?;
                write!(f, " ")?;
                let snake = Snake::up_line_up(incoming_width + width2(&parts.inside) + 1);
                (self.paint)(f, style, &snake)?;
                writeln!(f)?;

                incoming_style = Some(style);
            }
        }
        Ok(())
    }
}

impl<C: Display, T, S> LineParts<C, T, S> {
    fn code_parts(&self) -> impl Iterator<Item = (&C, &S)> {
        let inside = self.inside.iter().map(|(code, _label, styl)| (code, styl));
        let incoming = self.incoming.iter().map(|(code, _text, styl)| (code, styl));
        let outgoing = self.outgoing.iter().map(|(code, styl)| (code, styl));
        incoming.chain(inside).chain(outgoing)
    }
}

impl<T, S: Default> LineParts<Range<usize>, T, S> {
    fn segment(self, line: &str) -> LineParts<&str, T, S> {
        let len = line.len();
        let start = self.incoming.as_ref().map_or(0, |(code, ..)| code.end);
        let end = self.outgoing.as_ref().map_or(len, |(code, _)| code.start);
        let last = self.inside.last().map_or(start, |(code, ..)| code.end);

        let mut pos = start;
        let unlabelled =
            |start, end| (start < end).then(|| (&line[start..end], LabelKind::None, S::default()));
        let inside = self.inside.into_iter().flat_map(|(code, label, style)| {
            let unlabelled = unlabelled(pos, code.start);
            let labelled = (&line[code.start..code.end], label, style);
            pos = code.end;
            unlabelled.into_iter().chain([labelled])
        });
        LineParts {
            incoming: self
                .incoming
                .map(|(code, text, sty)| (&line[..code.end], text, sty)),
            inside: inside.chain(unlabelled(last, end)).collect(),
            outgoing: self.outgoing.map(|(code, sty)| (&line[code.start..], sty)),
        }
    }
}

impl<C, T, S> LineParts<C, T, S> {
    #[must_use]
    fn map_code<C1>(self, mut f: impl FnMut(C) -> C1) -> LineParts<C1, T, S> {
        let inside = self.inside.into_iter();
        LineParts {
            incoming: self.incoming.map(|(code, txt, sty)| (f(code), txt, sty)),
            inside: inside.map(|(code, lbl, sty)| (f(code), lbl, sty)).collect(),
            outgoing: self.outgoing.map(|(code, style)| (f(code), style)),
        }
    }
}

fn width<'a, C: 'a, T: 'a>(i: impl IntoIterator<Item = &'a (CodeWidth<C>, T)>) -> usize {
    i.into_iter().map(|(code, _)| code.width).sum()
}

fn width2<'a, C: 'a, T: 'a, S: 'a>(i: impl IntoIterator<Item = &'a (CodeWidth<C>, T, S)>) -> usize {
    i.into_iter().map(|(code, ..)| code.width).sum()
}

impl<C, T, S> LineParts<CodeWidth<C>, T, S> {
    /// Position of the end of the rightmost label.
    fn width(&self) -> usize {
        width2(&self.inside) + width2(&self.incoming) + width(&self.outgoing)
    }

    fn fmt_incoming(
        &self,
        paint: Paint<S>,
        style: &S,
        snake: Snake,
        f: &mut Formatter,
    ) -> fmt::Result {
        if let Some((code, _text, _style)) = &self.incoming {
            write!(f, "{}", " ".repeat(code.width))?;
            paint(f, style, snake.as_str())?;
        }
        Ok(())
    }

    fn fmt_inside<S1, S2>(
        &self,
        paint: Paint<S>,
        from: usize,
        s1: S1,
        s2: S2,
        f: &mut Formatter,
    ) -> fmt::Result
    where
        // display line for label without text
        S1: Fn(usize) -> String,
        // display line for label with text
        S2: Fn(usize, usize) -> String,
    {
        let before = width2(&self.inside[..from]);
        write!(f, "{}", " ".repeat(before))?;

        for (code, label, style) in &self.inside[from..] {
            match label {
                LabelKind::Text(_text) => {
                    let (left, right) = code.left_right();
                    paint(f, style, &s2(left, right))?;
                }
                LabelKind::Snake => paint(f, style, &s1(code.width))?,
                LabelKind::None => paint(f, style, &" ".repeat(code.width))?,
            }
        }
        Ok(())
    }

    /// Print something like "... ─┬─ ... ─┬─ ... ▲".
    fn fmt_arrows(&self, paint: Paint<S>, f: &mut Formatter) -> fmt::Result {
        self.fmt_inside(paint, 0, Snake::line, Snake::line_down_line, f)?;

        if let Some((_code, style)) = &self.outgoing {
            paint(f, style, Snake::ArrowUp.as_str())?;
        }
        Ok(())
    }

    /// Print something like "... │ ...  │"
    fn fmt_inside_vert(&self, paint: Paint<S>, from: usize, f: &mut Formatter) -> fmt::Result {
        let s1 = |w| " ".repeat(w);
        let s2 = |l, r| format!("{}{}{}", " ".repeat(l), Snake::Vertical, " ".repeat(r));
        self.fmt_inside(paint, from, s1, s2, f)?;

        if let Some((_code, style)) = &self.outgoing {
            paint(f, style, Snake::Vertical.as_str())?;
        }
        Ok(())
    }
}

/// Parts used to draw code spans and lines.
#[derive(Copy, Clone)]
enum Snake {
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

    /// "╰─...─╯"
    fn down_line_up(len: usize) -> String {
        format!("{}{}{}", Self::DownRight, Self::line(len), Self::RightUp)
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

    fn as_str(self) -> &'static str {
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
    }
}

impl Display for Snake {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}
