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
//! 1 │   (<span class=red>defun</span> <span class=green>factorial</span> (n) <span class=blue>(if (zerop n) 1</span>
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
//! This allows you to color labels as follows:
//!
//! ~~~
//! use codesnake::{Block, CodeWidth, Label, LineIndex};
//! use yansi::{Color, Paint};
//! # let src = r#"if true { 42 } else { "42" }"#;
//! # let idx = LineIndex::new(src);
//! # let range = 8..14;
//! let label = Label::<_, &str, _>::new(range).with_style(Color::Red);
//! # let block = Block::new(&idx, [label]).unwrap().map_code(|c| CodeWidth::new(c, c.len()));
//! let block = block.with_paint(|f, style, code| {
//!     if *style == Color::default() {
//!         write!(f, "{code}")
//!     } else {
//!         write!(f, "{}", code.fg(*style))
//!     }
//! });
//! assert_eq!(block.to_string(), "1 │ if true \u{1b}[31m{ 42 }\u{1b}[0m else { \"42\" }\n");
//! ~~~
//!
//! For HTML, you can use something like:
//!
//! ~~~
//! use codesnake::{Block, CodeWidth, Label, LineIndex};
//! # let src = r#"if true { 42 } else { "42" }"#;
//! # let idx = LineIndex::new(src);
//! # let range = 8..14;
//! let label = Label::<_, &str, _>::new(range).with_style("color:red");
//! # let block = Block::new(&idx, [label]).unwrap().map_code(|c| CodeWidth::new(c, c.len()));
//! let block = block.with_paint(|f, style, code| {
//!     if style.is_empty() {
//!         write!(f, "{code}")
//!     } else {
//!         write!(f, "<span style=\"{style}\">{code}</span>")
//!     }
//! });
//! assert_eq!(block.to_string(), "1 │ if true <span style=\"color:red\">{ 42 }</span> else { \"42\" }\n");
//! ~~~

extern crate alloc;

use alloc::vec::Vec;
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

/// Functions that determine what to print below labels.
struct Fns {
    /// display line for label without text
    snake: Option<fn(&mut Formatter, usize) -> fmt::Result>,
    /// display line for label with text
    text: fn(&mut Formatter, usize, usize) -> fmt::Result,
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
            kind: LabelKind::None,
            style: S::default(),
        }
    }
}

impl<C, T, S> Label<C, T, S> {
    /// Create a snake label with text.
    #[must_use]
    pub fn with_text(self, text: T) -> Self {
        let kind = LabelKind::Text(text);
        Self { kind, ..self }
    }

    /// Create a snake label without text.
    #[must_use]
    pub fn with_snake(self) -> Self {
        let kind = LabelKind::Snake;
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

type Paint<S> = fn(&mut Formatter, &S, &dyn Display) -> fmt::Result;

fn styled<'a, S>(paint: Paint<S>, style: &'a S, x: &'a impl Display) -> impl Display + 'a {
    from_fn(move |f| paint(f, style, x))
}

struct FromFn<F>(F);

fn from_fn<F: Fn(&mut Formatter) -> fmt::Result>(f: F) -> FromFn<F> {
    FromFn(f)
}

impl<F: Fn(&mut Formatter) -> fmt::Result> Display for FromFn<F> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        (self.0)(f)
    }
}

enum LabelKind<T> {
    None,
    Snake,
    Text(T),
}

/// Sequence of lines, containing code `C`, (label) text `T`, and style `S`.
pub struct Block<C, T, S> {
    lines: Vec<Line<C, T, S>>,
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
                Some((line_no, _line, parts)) if line_no == start.line_no => parts,
                Some(line) => {
                    lines.push(line);
                    LineParts::default()
                }
                None => LineParts::default(),
            };

            if start.line_no == end.line_no {
                parts.inside.push((start.bytes..end.bytes, kind, style));
                lines.push((start.line_no, start.line, parts));
            } else {
                let range = start.bytes..start.line.len();
                if kind.has_snake() {
                    parts.outgoing = Some((range, style.clone()));
                } else {
                    parts.inside.push((range, LabelKind::None, style.clone()));
                }
                lines.push((start.line_no, start.line, parts));

                for line_no in start.line_no + 1..end.line_no {
                    let line = idx.0[line_no].1;
                    let parts = LineParts {
                        inside: Vec::from([(0..line.len(), LabelKind::None, style.clone())]),
                        ..Default::default()
                    };
                    lines.push((line_no, line, parts));
                }

                let mut parts = LineParts::default();
                let range = 0..end.bytes;
                if kind.has_snake() {
                    parts.incoming = Some((range, kind.text(), style.clone()));
                } else {
                    parts.inside.push((range, LabelKind::None, style.clone()));
                }
                lines.push((end.line_no, end.line, parts));
            }
        }

        let lines = lines.into_iter().map(|(no, line, parts)| Line {
            no,
            parts: parts.segment(line),
        });
        Some(Block {
            lines: lines.collect(),
            paint: |f, _, s| write!(f, "{s}"),
        })
    }
}

impl<C, T, S> Block<C, T, S> {
    /// Apply function to code.
    #[must_use]
    pub fn map_code<C1>(self, mut f: impl FnMut(C) -> C1) -> Block<C1, T, S> {
        Block {
            lines: self.lines.into_iter().map(|l| l.map_code(&mut f)).collect(),
            paint: self.paint,
        }
    }

    fn some_incoming(&self) -> bool {
        self.lines.iter().any(|line| line.parts.incoming.is_some())
    }

    fn line_no_width(&self) -> usize {
        let max = self.lines.last().unwrap().no + 1;
        // number of digits; taken from https://stackoverflow.com/a/69302957
        core::iter::successors(Some(max), |&n| (n >= 10).then_some(n / 10)).count()
    }

    /// Line that precedes the block, i.e. " ... ╭─".
    #[must_use]
    pub fn prologue(&self) -> impl Display {
        let space = space(self.line_no_width());
        from_fn(move |f| write!(f, "{space} {}{}", Snake::UpRight, Snake::Horizontal))
    }

    /// Line number space followed by a vertical snake, i.e. " ... |".
    ///
    /// This is useful after the prologue, to make things less cramped.
    #[must_use]
    pub fn space_vert(&self) -> impl Display {
        let space = space(self.line_no_width());
        from_fn(move |f| write!(f, "{space} {}", Snake::Vertical))
    }

    /// Line that succeeds the block, i.e. "─...─╯".
    #[must_use]
    pub fn epilogue(&self) -> impl Display {
        Snake::line_up(self.line_no_width() + 1)
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
}

fn space(width: usize) -> impl Display {
    from_fn(move |f| write!(f, "{:width$}", ""))
}

macro_rules! width {
    ($slice:expr) => {
        $slice.iter().map(|(code, ..)| code.width).sum::<usize>()
    };
}

impl<C: Display, T: Display, S> Display for Block<CodeWidth<C>, T, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let paint = self.paint;
        let mut incoming_style: Option<&S> = None;
        let mut prev_line_no = None;

        let line_no_width = self.line_no_width();
        let line_no_space = space(line_no_width);
        // " ...  ┆"
        let dots = from_fn(move |f| write!(f, "{line_no_space} {}", Snake::VerticalDots));

        let incoming_space = if self.some_incoming() { "  " } else { "" };

        for line @ Line { parts, .. } in &self.lines {
            if prev_line_no.filter(|prev| *prev + 1 < line.no).is_some() {
                writeln!(f, "{dots}")?;
            }
            prev_line_no = Some(line.no);

            // write line number right-aligned
            write!(f, "{:>line_no_width$} │", line.no + 1)?;

            if let Some(style) = incoming_style {
                write!(f, " {}", styled(paint, style, &Snake::Vertical))?;
            } else {
                incoming_space.fmt(f)?;
            }

            write!(f, " ")?;
            parts.code_parts().try_for_each(|(c, s)| paint(f, s, c))?;
            writeln!(f)?;

            // print the line just below the code, e.g.
            // " ...  ┆ │ ... ─┬─ ... ─┬─ ... ▲"
            if parts.arrows_below() {
                write!(f, "{dots} ")?;
                if let Some(style) = incoming_style {
                    styled(paint, style, &Snake::Vertical).fmt(f)?;
                    parts.incoming(paint, Snake::ArrowUp).fmt(f)?;
                } else {
                    incoming_space.fmt(f)?;
                }
                writeln!(f, "{}", parts.arrows(paint))?;
            }

            if parts.incoming.is_some() {
                assert!(incoming_style.take().is_some());
                parts.incoming_text(&dots, paint).fmt(f)?;
            }

            let incoming_width = width!(parts.incoming);
            let prefix = from_fn(|f| write!(f, "{dots}{incoming_space} {}", space(incoming_width)));
            parts.inside_text(&prefix, paint).fmt(f)?;

            // " ...  ┆ ╭─...─╯"
            if let Some((_, style)) = &parts.outgoing {
                let snake = Snake::up_line_up(incoming_width + width!(parts.inside) + 1);
                writeln!(f, "{dots} {}", styled(paint, style, &snake))?;

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

impl<C, T, S> LineParts<CodeWidth<C>, T, S> {
    /// Position of the end of the rightmost label.
    fn width(&self) -> usize {
        width!(self.inside) + width!(self.incoming) + width!(self.outgoing)
    }

    fn incoming<'a>(&'a self, paint: Paint<S>, snake: Snake) -> impl Display + 'a {
        from_fn(move |f| {
            if let Some((code, _text, style)) = &self.incoming {
                space(code.width).fmt(f)?;
                paint(f, style, &snake)?;
            }
            Ok(())
        })
    }

    fn outgoing<'a>(&'a self, paint: Paint<S>, snake: Snake) -> impl Display + 'a {
        from_fn(move |f| {
            if let Some((_code, style)) = &self.outgoing {
                paint(f, style, &snake)?;
            }
            Ok(())
        })
    }

    fn inside<'a>(&'a self, paint: Paint<S>, from: usize, fns: &'a Fns) -> impl Display + 'a {
        from_fn(move |f| {
            space(width!(self.inside[..from])).fmt(f)?;

            for (code, label, style) in &self.inside[from..] {
                match label {
                    LabelKind::Text(_text) => {
                        let (left, right) = code.left_right();
                        paint(f, style, &from_fn(|f| (fns.text)(f, left, right)))
                    }
                    LabelKind::Snake => match fns.snake {
                        Some(snake) => paint(f, style, &from_fn(|f| (snake)(f, code.width))),
                        None => space(code.width).fmt(f),
                    },
                    LabelKind::None => space(code.width).fmt(f),
                }?;
            }
            Ok(())
        })
    }

    /// Print something like "... ─┬─ ... ─┬─ ... ▲".
    fn arrows(&self, paint: Paint<S>) -> impl Display + '_ {
        let fns = Fns {
            snake: Some(|f, w| Snake::line(w).fmt(f)),
            text: |f, l, r| Snake::line_down_line(l, r).fmt(f),
        };
        let outgoing = self.outgoing(paint, Snake::ArrowUp);
        from_fn(move |f| write!(f, "{}{outgoing}", self.inside(paint, 0, &fns)))
    }

    /// Print something like "... │ ...  │"
    fn inside_vert(&self, paint: Paint<S>, from: usize) -> impl Display + '_ {
        let fns = Fns {
            snake: None,
            text: |f, l, r| write!(f, "{}{}{}", space(l), Snake::Vertical, space(r)),
        };
        let outgoing = self.outgoing(paint, Snake::Vertical);
        from_fn(move |f| write!(f, "{}{outgoing}", self.inside(paint, from, &fns)))
    }
}

impl<C, T: Display, S> LineParts<CodeWidth<C>, T, S> {
    /// Print text snakes below inside parts.
    ///
    /// ~~~ text
    ///   ┆ │   │
    ///   ┆ ╰────── text1
    ///   ┆     │
    ///   ┆     ╰── text2
    /// ~~~
    fn inside_text<'a>(&'a self, prefix: &'a impl Display, paint: Paint<S>) -> impl Display + 'a {
        from_fn(move |f| {
            let mut before = 0;
            for (i, (code, label, style)) in self.inside.iter().enumerate() {
                if let LabelKind::Text(text) = label {
                    // "... │ ... │"
                    writeln!(f, "{prefix}{}", self.inside_vert(paint, i))?;

                    // "╰─...─ {text}"
                    let (left, right) = code.left_right();
                    let after = width!(self.inside) - before - code.width + width!(self.outgoing);
                    let space = space(before + left);
                    let snake = Snake::down_line(right + after + 1);
                    writeln!(f, "{prefix}{space}{} {text}", styled(paint, style, &snake))?;
                }
                before += code.width;
            }
            Ok(())
        })
    }

    /// Print snakes below incoming parts.
    ///
    /// ~~~ text
    ///   ┆ │   │   │
    ///   ┆ ╰───┴────── text
    /// ~~~
    ///
    /// Or:
    ///
    /// ~~~ text
    ///   ┆ │   │   │
    ///   ┆ ╰───╯   |
    /// ~~~
    fn incoming_text<'a>(&'a self, dots: &'a impl Display, paint: Paint<S>) -> impl Display + 'a {
        from_fn(move |f| {
            if let Some((code, text, style)) = &self.incoming {
                let snake = styled(paint, style, &Snake::Vertical);
                let incoming = self.incoming(paint, Snake::Vertical);
                writeln!(f, "{dots} {snake}{incoming}{}", self.inside_vert(paint, 0))?;

                if let Some(text) = text {
                    let snake = Snake::down_line_up_line(code.width, self.width() + 1 - code.width);
                    let snake = styled(paint, style, &snake);
                    writeln!(f, "{dots} {snake} {text}")
                } else {
                    let snake = Snake::down_line_up(code.width);
                    let snake = styled(paint, style, &snake);
                    writeln!(f, "{dots} {snake}{}", self.inside_vert(paint, 0))
                }?
            }
            Ok(())
        })
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
    fn line(len: usize) -> impl Display {
        from_fn(move |f| write!(f, "{:─>len$}", ""))
    }

    /// ╰─...─
    fn down_line(len: usize) -> impl Display {
        from_fn(move |f| write!(f, "{}{}", Snake::DownRight, Snake::line(len)))
    }

    /// ╰─...─┴─...─
    fn down_line_up_line(l: usize, r: usize) -> impl Display {
        let l = Self::line(l);
        let r = Self::line(r);
        from_fn(move |f| write!(f, "{}{l}{}{r}", Self::DownRight, Self::HorizontalUp,))
    }

    /// "╰─...─╯"
    fn down_line_up(len: usize) -> impl Display {
        from_fn(move |f| write!(f, "{}{}{}", Self::DownRight, Self::line(len), Self::RightUp))
    }

    /// "╭─...─╯"
    fn up_line_up(len: usize) -> impl Display {
        from_fn(move |f| write!(f, "{}{}{}", Self::UpRight, Self::line(len), Self::RightUp))
    }

    /// "─...─╯"
    fn line_up(len: usize) -> impl Display {
        from_fn(move |f| write!(f, "{}{}", Self::line(len), Self::RightUp))
    }

    /// ─...─┬─...─
    fn line_down_line(l: usize, r: usize) -> impl Display {
        let l = Self::line(l);
        let r = Self::line(r);
        from_fn(move |f| write!(f, "{l}{}{r}", Self::HorizontalDown,))
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
