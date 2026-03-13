// To generate SVG from this example:
//
//     cargo run --example example | ansisvg --colorscheme "Builtin Solarized Dark" --fontname "Source Code Pro" --fontsize 18 > example.svg
use codesnake::{Block, CodeWidth, Label, LineIndex};
use core::fmt::{self, Display, Formatter};
use yansi::{Color, Paint};

const SRC: &str = r#"(defun factorial (n) (if (zerop n) 1
        (* n (factorial (1- n)))))"#;

fn paint_html(f: &mut Formatter, color: &Color, s: &dyn Display) -> fmt::Result {
    let mut color = format!("{color:?}");
    color.make_ascii_lowercase();
    write!(f, "<span style=\"color:{color}\">{s}</span>")
}

fn paint_ansi(f: &mut Formatter, color: &Color, s: &dyn Display) -> fmt::Result {
    s.fg(*color).fmt(f)
}


fn main() {
    /* to find the byte positions in this example:
    for ci in SRC.char_indices() {
        println!("{ci:?}");
    }
    */

    let html = std::env::args().skip(1).any(|arg| arg == "--html");
    let idx = LineIndex::new(SRC);
    let paint = if html { paint_html } else { paint_ansi };

    let labels = [
        Label::new(1..6).with_style(Color::Red),
        Label::new(7..16)
            .with_text("this function ...")
            .with_style(Color::Green),
        Label::new(21..70)
            .with_text("... is defined by this")
            .with_style(Color::Blue),
        Label::new(71..71)
            .with_text("(and here is EOF)")
            .with_style(Color::Yellow),
    ];
    let block = Block::new(&idx, labels).unwrap();
    let block = block.with_paint(paint).map_code(|s| {
        let s = s.replace('\t', "    ");
        let w = unicode_width::UnicodeWidthStr::width(&*s);
        CodeWidth::new(s, core::cmp::max(w, 1))
    });

    println!(
        "{}{}",
        block.prologue(),
        fmt_for_older_rust::from_fn(|f| paint(f, &Color::Red, &"[fac.lisp]"))
        //>= 1.93 fmt::from_fn(|f| paint(f, &Color::Red, &"[fac.lisp]"))
    );
    print!("{block}");
    println!("{}", block.epilogue());
}


// stablilized in rust 1.93
// Starting 1.93, just use fmt::from_fn instead of fmt_for_older_rust:from_fn
mod fmt_for_older_rust {
    use core::fmt;

    /// Creates a value that implements [`fmt::Debug`] and [`fmt::Display`] via the provided closure.
    ///
    /// This is a backport of the stabilized `fmt::from_fn` function, which is available in Rust
    /// 1.93 and later.
    #[must_use = "returns a type implementing Debug and Display, which do not have any effects unless they are used"]
    pub fn from_fn<F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result>(f: F) -> FromFn<F> {
        FromFn(f)
    }

    /// Implements [`fmt::Debug`] and [`fmt::Display`] via the provided closure.
    ///
    /// Created with [`from_fn`].
    pub struct FromFn<F>(F);

    impl<F> fmt::Debug for FromFn<F>
    where
        F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (self.0)(f)
        }
    }

    impl<F> fmt::Display for FromFn<F>
    where
        F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (self.0)(f)
        }
    }
}

