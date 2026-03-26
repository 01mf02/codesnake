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

    let block = Block::new(&idx, labels).unwrap();
    let block = block.with_paint(paint).map_code(|s| {
        let s = s.replace('\t', "    ");
        let w = unicode_width::UnicodeWidthStr::width(&*s);
        CodeWidth::new(s, core::cmp::max(w, 1))
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
// * t: text
// * s: snake
// * n: none
// * b: break (omitted lines)
//
// followed by a number that indicates how many lines a label spans

#[test]
fn s1() {
    assert_eq!(
        format(SRC, [Label::new(4..7).with_snake()]),
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
fn s1s1_including_newline() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..8).with_snake(),
                Label::new(12..16).with_snake()
            ]
        ),
        "
  ╭─
  │
1 │ foo bar
  ┆     ───
2 │ baz toto
  ┆     ────
──╯
"
    );
}

#[test]
fn s1s1() {
    assert_eq!(
        format(
            SRC,
            [Label::new(0..3).with_snake(), Label::new(4..7).with_snake()]
        ),
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
fn s1s2() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(0..3).with_snake(),
                Label::new(4..11).with_snake()
            ]
        ),
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
fn t1t2t1() {
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
fn s3() {
    assert_eq!(
        format(SRC, [Label::new(4..21).with_snake()]),
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
fn s3s1() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..21).with_snake(),
                Label::new(25..34).with_text("thanks for all the ...")
            ]
        ),
        "
  ╭─
  │
1 │   foo bar
  ┆       ▲
  ┆ ╭─────╯
2 │ │ baz toto
3 │ │ look, a fish 🐟 and a hook 🪝
  ┆ │    ▲    ───┬───              
  ┆ │    │       │                 
  ┆ ╰────╯       │                 
  ┆              │                 
  ┆              ╰────────────────── thanks for all the ...
──╯
"
    );
}

#[test]
fn t1t1() {
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
fn t2t2() {
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
fn adjacent() {
    assert_eq!(
        format(
            SRC,
            [Label::new(0..3).with_snake(), Label::new(3..7).with_snake()]
        ),
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
fn n1() {
    assert_eq!(
        format(SRC, [Label::new(25..34)]),
        "
  ╭─
  │
3 │ look, a fish 🐟 and a hook 🪝
──╯
"
    );
}

#[test]
fn n1t1() {
    assert_eq!(
        format(
            SRC,
            [Label::new(24..25), Label::new(25..26).with_text("hello")]
        ),
        "
  ╭─
  │
3 │ look, a fish 🐟 and a hook 🪝
  ┆         ┬                    
  ┆         │                    
  ┆         ╰───────────────────── hello
──╯
"
    );
}

#[test]
fn t2t2n1() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..11).with_text("ba?"),
                Label::new(12..21).with_text("four-letter words"),
                Label::new(72..72),
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
fn n1t2n1() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..11),
                Label::new(12..21).with_text("four-letter words"),
                Label::new(72..72),
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
fn n4() {
    assert_eq!(
        format(SRC, [Label::new(0..72)]),
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
fn n4_style() {
    assert_eq!(
        format(SRC, [Label::new(0..72).with_style(true)]),
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
fn n1bt1n1() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(4..5),
                Label::new(25..26).with_text("hello"),
                Label::new(70..71),
            ],
        ),
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
fn n1bn1() {
    assert_eq!(
        format(SRC, [Label::new(4..5), Label::new(70..71)]),
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
fn n1bs1() {
    assert_eq!(
        format(SRC, [Label::new(4..5), Label::new(67..72).with_snake()]),
        "
  ╭─
  │
1 │ foo bar
  ┆
4 │ this is getting silly
  ┆                 ─────
──╯
"
    );
}

#[test]
fn n1bs1_style() {
    assert_eq!(
        format(
            SRC,
            [
                Label::new(0..3).with_style(true),
                Label::new(67..72).with_snake(),
            ],
        ),
        "
  ╭─
  │
1 │ <span>foo</span> bar
  ┆
4 │ this is getting silly
  ┆                 ─────
──╯
"
    );
}

#[test]
fn s1bn1() {
    assert_eq!(
        format(SRC, [Label::new(4..5).with_snake(), Label::new(70..71)],),
        "
  ╭─
  │
1 │ foo bar
  ┆     ─  
  ┆
4 │ this is getting silly
──╯
"
    );
}
