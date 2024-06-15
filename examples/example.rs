use codesnake::{Block, CodeWidth, Label, LineIndex};
use core::fmt::Display;
use yansi::{Color, Paint};

const SRC: &str = r#"if true { 42 } else { "42" }"#;

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
        Label::new(8..14, "this is of type Nat").with_style(color(Color::Green)),
        Label::new(20..28, "this is of type String").with_style(color(Color::Blue)),
    ];
    let block = Block::new(&idx, labels).unwrap().map_code(|s| {
        let s = s.replace('\t', "    ");
        let w = unicode_width::UnicodeWidthStr::width(&*s);
        CodeWidth::new(s, w)
    });
    println!(
        "{}{}",
        block.prologue(),
        style(html, &"[main.rs]", Color::Red)
    );
    print!("{block}");
    println!("{}", block.epilogue());
}
