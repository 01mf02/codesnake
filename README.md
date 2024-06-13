# codesnake

codesnake is a Rust crate that shows code blocks and labels parts of it.
Its name comes from the snake-like appearance of
the lines that connect code spans with their corresponding labels.
An example of its output:

<style>
pre span.red   { color: #dc322f; }
pre span.green { color: #859900; }
pre span.blue  { color: #268bd2; }
</style>
<pre style="background-color:#002b36; color:#93a1a1; line-height:1.0; font-size:x-large;">
  ╭─<span class=red>[main.rs]</span>
  │
1 │ if true { 42 } else { "42" }
  ┆         <span class=green>───</span><span class=green>┬</span><span class=green>──</span>      <span class=blue>────</span><span class=blue>┬</span><span class=blue>───</span>
  ┆            <span class=green>│</span>            <span class=blue>│</span>
  ┆            <span class=green>╰</span><span class=green>─────────────────</span> this is of type Nat
  ┆                         <span class=blue>│</span>
  ┆                         <span class=blue>╰</span><span class=blue>────</span> this is of type String
──╯
</pre>

## Features

* Uses `&str` as code input and byte positions for spans
* Multiple spans within a code block
* Spans may range over multiple lines
* Zero dependencies

While this crate does not support colored output out of the box,
it is very easy to integrate it with other crates like `yansi`
to produce colored output for the terminal (ANSI) and web (HTML).

## Related crates

* [`ariadne`](https://crates.io/crates/ariadne):
  I used ariadne happily myself for quite some time, but it had
  [broken semantic versioning](https://github.com/zesterer/ariadne/issues/116)
  for at least one month now, which led to build failures in a project of mine.
  Furthermore, the heart of this crate is a function more than 700 lines long,
  of which the author himself states that it
  [is complex, has bugs and needs rewriting][write.rs].
  codesnake can be considered to be a rewrite of ariadne, focusing on its core features.
* [codespan-reporting](https://crates.io/crates/codespan-reporting):
  This seems to be the spiritual predecessor of ariadne,
  but it looks unfortunately unmaintained, with the last release from 2021.
* [`miette`](https://crates.io/crates/miette):
  This seems to be a pretty popular library nowadays for code span reporting.
  However, to me it looks intimidatingly complex and
  provides much more functionality than I need.
  Furthermore, it has a higher MSRV and more dependencies than I like.
  But, the real deal breaker for me is that according to its description, it is
  "for us mere mortals who aren't compiler hackers".
  Given that I see myself as some kind of compiler hacker,
  I do not feel as part of its target group (although I'm probably mortal). :)

[write.rs]: https://github.com/zesterer/ariadne/blob/876a093653bdbe7b69f4e77cd122fed5caa37a27/src/write.rs#L10
