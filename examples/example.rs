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

    let filename = from_fn(|f| paint(f, &Color::Red, &"[fac.lisp]"));
    println!("{}{filename}", block.prologue());
    println!("{}", block.space_vert());
    print!("{block}");
    println!("{}", block.epilogue());
}

// available starting from Rust 1.93 as [`core::fmt::from_fn`]
fn from_fn<F: Fn(&mut Formatter) -> fmt::Result>(f: F) -> FromFn<F> {
    FromFn(f)
}

struct FromFn<F>(F);

impl<F: Fn(&mut Formatter) -> fmt::Result> Display for FromFn<F> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        (self.0)(f)
    }
}
