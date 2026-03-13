use codesnake::{Block, CodeWidth, Label, LineIndex};
use core::fmt::{self, Display, Formatter};
use core::ops::Range;
use pretty_assertions::assert_eq;

fn paint(f: &mut Formatter, style: &bool, s: &dyn Display) -> fmt::Result {
    if *style {
        write!(f, "<span>{s}</span>")
    } else {
        write!(f, "{s}")
    }
}

fn format<const N: usize>(code: &str, labels: [Label<Range<usize>, &str, bool>; N]) -> String {
    let idx = LineIndex::new(code);

    let mut prev_empty = false;
    let block = Block::new(&idx, labels).unwrap();
    let block = block.with_paint(paint).map_code(|s| {
        let sub = usize::from(core::mem::replace(&mut prev_empty, s.is_empty()));
        let s = s.replace('\t', "    ");
        let w = unicode_width::UnicodeWidthStr::width(&*s);
        CodeWidth::new(s, core::cmp::max(w, 1) - sub)
    });
    format!(
        "\n{}\n{}\n{block}{}\n",
        block.prologue(),
        block.space_vert(),
        block.epilogue()
    )
}

fn main() {
    // to find the byte positions in this example
    for ci in SRC.char_indices() {
        println!("{ci:?}");
    }
    println!("{}", format(SRC, [Label::new(4..7)]));
}

const SRC: &str = "foo bar\nbaz toto\nlook, a fish 🐟 and a hook 🪝\nthis is getting silly";

// nomenclature:
//
// * s: single-line
// * m: multi-line
// * t: text
// * n: no text

#[test]
fn sn() {
    assert_eq!(
        format(SRC, [Label::new(4..7)]),
        "
  ╭─
  │
1 │ foo bar
  ┆     ───
──╯
"
    );
}

#[test]
fn snsn() {
    assert_eq!(
        format(SRC, [Label::new(0..3), Label::new(4..7)]),
        "
  ╭─
  │
1 │ foo bar
  ┆ ─── ───
──╯
"
    );
}

#[test]
fn snmn() {
    assert_eq!(
        format(SRC, [Label::new(0..3), Label::new(4..11)]),
        "
  ╭─
  │
1 │   foo bar
  ┆   ─── ▲
  ┆ ╭─────╯
2 │ │ baz toto
  ┆ │   ▲     
  ┆ │   │     
  ┆ ╰───╯     
──╯
"
    );
}

#[test]
fn stmtst() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(0..3).with_text("some foo"),
                Label::new(4..11).with_text("more"),
                Label::new(12..16).with_text("a band?")
            ]
        ),
        "
  ╭─
  │
1 │   foo bar
  ┆   ─┬─ ▲
  ┆    │  │
  ┆    ╰────── some foo
  ┆ ╭─────╯
2 │ │ baz toto
  ┆ │   ▲ ──┬─
  ┆ │   │   │ 
  ┆ ╰───┴────── more
  ┆         │ 
  ┆         ╰── a band?
──╯
"
    );
}

#[test]
fn mmn() {
    assert_eq!(
        format(SRC, [Label::new(4..21)]),
        "
  ╭─
  │
1 │   foo bar
  ┆       ▲
  ┆ ╭─────╯
2 │ │ baz toto
3 │ │ look, a fish 🐟 and a hook 🪝
  ┆ │    ▲                         
  ┆ │    │                         
  ┆ ╰────╯                         
──╯
"
    );
}

#[test]
fn stst() {
    let labels = [
        Label::new(25..34).with_text("animal"),
        Label::new(41..50).with_text("object"),
    ];
    let output = "
  ╭─
  │
3 │ look, a fish 🐟 and a hook 🪝
  ┆         ───┬───       ───┬───
  ┆            │             │   
  ┆            ╰────────────────── animal
  ┆                          │   
  ┆                          ╰──── object
──╯
";
    assert_eq!(format(SRC, labels), output);
}

#[test]
fn mtmt() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..11).with_text("ba?"),
                Label::new(12..21).with_text("four-letter words")
            ]
        ),
        "
  ╭─
  │
1 │   foo bar
  ┆       ▲
  ┆ ╭─────╯
2 │ │ baz toto
  ┆ │   ▲ ▲
  ┆ │   │ │
  ┆ ╰───┴────── ba?
  ┆ ╭─────╯
3 │ │ look, a fish 🐟 and a hook 🪝
  ┆ │    ▲                         
  ┆ │    │                         
  ┆ ╰────┴────────────────────────── four-letter words
──╯
"
    );
}

#[test]
fn empty() {
    assert_eq!(
        format(SRC, [Label::new(2..2), Label::new(4..7)]),
        "
  ╭─
  │
1 │ foo bar
  ┆   ─ ───
──╯
"
    );
}

#[test]
fn adjacent() {
    assert_eq!(
        format(SRC, [Label::new(0..3), Label::new(3..7)]),
        "
  ╭─
  │
1 │ foo bar
  ┆ ───────
──╯
"
    );
}

#[test]
fn the_end() {
    assert_eq!(
        format(SRC, [Label::new(72..72).with_text("the end")]),
        "
  ╭─
  │
4 │ this is getting silly
  ┆                      ┬
  ┆                      │
  ┆                      ╰─ the end
──╯
"
    );
}

#[test]
fn the_end_plus_unmarked() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(25..34).unmarked(),
                Label::new(72..72).with_text("the end"),
            ]
        ),
        "
  ╭─
  │
3 │ look, a fish 🐟 and a hook 🪝
4 │ this is getting silly
  ┆                      ┬
  ┆                      │
  ┆                      ╰─ the end
──╯
"
    );
}

#[test]
fn the_end_plus_unmarked_with_snake() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(24..24).unmarked(),
                Label::new(25..25).with_text("hello"),
                Label::new(72..72).with_text("the end"),
            ]
        ),
        "
  ╭─
  │
3 │ look, a fish 🐟 and a hook 🪝
  ┆         ┬                    
  ┆         │                    
  ┆         ╰───────────────────── hello
4 │ this is getting silly
  ┆                      ┬
  ┆                      │
  ┆                      ╰─ the end
──╯
"
    );
}

#[test]
fn mtmt_unmarked() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..11).with_text("ba?"),
                Label::new(12..21).with_text("four-letter words"),
                Label::new(72..72).unmarked(),
            ]
        ),
        "
  ╭─
  │
1 │   foo bar
  ┆       ▲
  ┆ ╭─────╯
2 │ │ baz toto
  ┆ │   ▲ ▲
  ┆ │   │ │
  ┆ ╰───┴────── ba?
  ┆ ╭─────╯
3 │ │ look, a fish 🐟 and a hook 🪝
  ┆ │    ▲                         
  ┆ │    │                         
  ┆ ╰────┴────────────────────────── four-letter words
4 │   this is getting silly
──╯
"
    );
}

#[test]
fn utmtu() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..11).unmarked(),
                Label::new(12..21).with_text("four-letter words"),
                Label::new(72..72).unmarked(),
            ]
        ),
        "
  ╭─
  │
1 │   foo bar
2 │   baz toto
  ┆       ▲
  ┆ ╭─────╯
3 │ │ look, a fish 🐟 and a hook 🪝
  ┆ │    ▲                         
  ┆ │    │                         
  ┆ ╰────┴────────────────────────── four-letter words
4 │   this is getting silly
──╯
"
    );
}

#[test]
fn u() {
    assert_eq!(
        format(SRC, [Label::new(0..72).unmarked(),]),
        "
  ╭─
  │
1 │ foo bar
2 │ baz toto
3 │ look, a fish 🐟 and a hook 🪝
4 │ this is getting silly
──╯
"
    );
}

#[test]
fn u_style() {
    assert_eq!(
        format(SRC, [Label::new(0..72).unmarked().with_style(true)]),
        "
  ╭─
  │
1 │ <span>foo bar</span>
2 │ <span>baz toto</span>
3 │ <span>look, a fish 🐟 and a hook 🪝</span>
4 │ <span>this is getting silly</span>
──╯
"
    );
}

#[test]
fn utu() {
    let should = format(
        SRC,
        [
            Label::new(4..4).unmarked(),
            Label::new(25..25).with_text("hello"),
            Label::new(70..70).unmarked(),
        ],
    );
    println!("{should}");
    assert_eq!(
        should,
        "
  ╭─
  │
1 │ foo bar
  ┆
3 │ look, a fish 🐟 and a hook 🪝
  ┆         ┬                    
  ┆         │                    
  ┆         ╰───────────────────── hello
4 │ this is getting silly
──╯
"
    );
}
#[test]
fn u_u() {
    let should = format(
        SRC,
        [Label::new(4..4).unmarked(), Label::new(70..70).unmarked()],
    );
    println!("{should}");
    assert_eq!(
        should,
        "
  ╭─
  │
1 │ foo bar
  ┆
4 │ this is getting silly
──╯
"
    );
}
#[test]
fn u_t() {
    let should = format(
        SRC,
        [
            Label::new(4..4).unmarked(),
            Label::new(70..70).with_text("!"),
        ],
    );
    println!("{should}");
    assert_eq!(
        should,
        "
  ╭─
  │
1 │ foo bar
  ┆
4 │ this is getting silly
  ┆                    ┬ 
  ┆                    │ 
  ┆                    ╰── !
──╯
"
    );
}

#[test]
fn u_t_style() {
    let should = format(
        SRC,
        [
            Label::new(0..3).unmarked().with_style(true),
            Label::new(70..70).with_text("!"),
        ],
    );
    println!("{should}");
    assert_eq!(
        should,
        "
  ╭─
  │
1 │ <span>foo</span> bar
  ┆
4 │ this is getting silly
  ┆                    ┬ 
  ┆                    │ 
  ┆                    ╰── !
──╯
"
    );
}

#[test]
fn m_u() {
    let should = format(
        SRC,
        [
            Label::new(4..4).with_text("hello"),
            Label::new(70..70).unmarked(),
        ],
    );
    println!("{should}");
    assert_eq!(
        should,
        "
  ╭─
  │
1 │ foo bar
  ┆     ┬  
  ┆     │  
  ┆     ╰─── hello
  ┆
4 │ this is getting silly
──╯
"
    );
}
