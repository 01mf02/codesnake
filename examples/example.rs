use codesnake::{Block, CodeWidth, Label, LineIndex};
use core::fmt::Display;
use yansi::{Color, Paint};

const SRC: &str = r#"(defun factorial (n) (if (zerop n) 1
        (* n (factorial (1- n)))))"#;

fn style(html: bool, d: &impl Display, color: Color) -> String {
    if html {
        let mut color = format!("{color:?}");
        color.make_ascii_lowercase();
        format!("<span class={color}>{d}</span>",)
    } else {
        d.fg(color).to_string()
    }
}

fn main() {
    /* to find the byte positions in this example:
    for ci in SRC.char_indices() {
        println!("{ci:?}");
    }
    */

    let html = std::env::args().skip(1).any(|arg| arg == "--html");
    let idx = LineIndex::new(SRC);
    let color = |color| move |s| style(html, &s, color);

    let labels = [
        Label::new(7..16, "this function ...").with_style(color(Color::Green)),
        Label::new(21..70, "... is defined by this").with_style(color(Color::Blue)),
        Label::new(71..71, "(and here is EOF)").with_style(color(Color::Yellow)),
    ];
    let block = Block::new(&idx, labels).unwrap().segment().map_code(|s| {
        let s = s.replace('\t', "    ");
        let w = unicode_width::UnicodeWidthStr::width(&*s);
        CodeWidth::new(s, core::cmp::max(w, 1))
    });
    println!(
        "{}{}",
        block.prologue(),
        style(html, &"[fac.lisp]", Color::Red)
    );
    print!("{block}");
    println!("{}", block.epilogue());
}
