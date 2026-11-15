# markdown

CommonMark 0.31.2 to HTML in pure Bend. All 652 spec examples pass.

```bend
import bend-kit-markdown@0.2.0.0/markdown.bend as M
```

```bend
def main() -> IO(Unit):
  # <h1>Hi &amp; <em>bye</em></h1>
  # <ul>
  # <li><a href="https://example.com">link</a></li>
  # </ul>
  IO.print(M.to_html("# Hi & *bye*\n\n- [link][x]\n\n[x]: https://example.com\n"))
```

`to_html(s: String) -> String` takes the whole document and returns HTML in the same form as the spec and cmark: `<p>`, `<em>`, `<strong>`, `<code>`, `<pre><code class="language-…">`, `<hr />`, `<br />`, and lists that are tight or loose. It cannot fail. Every input is a valid CommonMark document.

Text is HTML-escaped: `&`, `<`, `>`, and `"` become `&amp;`, `&lt;`, `&gt;`, and `&quot;`. Code spans and code blocks are escaped the same way. A link or image URL is percent-encoded where it is not a safe URL character, and `&` and `'` in it become `&amp;` and `&#x27;`. A title or alt text is escaped as text.

`to_html` does not sanitize. As CommonMark requires, raw HTML blocks and inline HTML pass through, and a `javascript:` URL stays a link.

For untrusted input, use `to_html_safe(s: String) -> String`. It renders as cmark does without `--unsafe`. Each raw HTML block and each inline HTML tag becomes `<!-- raw HTML omitted -->`. A link, image, or autolink URL that starts with `javascript:`, `vbscript:`, `file:`, or `data:`, in any ASCII case, becomes an empty `href` or `src`. A `data:image/png`, `data:image/gif`, `data:image/jpeg`, or `data:image/webp` URL stays. Text, titles, and alt text are escaped in both modes.

The input is a `String` of code points. Decode octets with `encoding`'s `utf8.decode` first. Tabs expand to the next multiple of 4 columns where block structure needs it. A NUL becomes U+FFFD. Link labels match after Unicode case folding, through `bend-kit-unicode`. Named character references use the HTML5 list in `entities.bend`.

GitHub extensions, such as tables, task lists, strikethrough, and autolinks without `<>`, are not supported.

## Spec tests

```sh
python3 markdown/conformance.py          # pass count per section, in a native build
python3 markdown/conformance.py Links    # also print the failures in one section
python3 markdown/conformance.py --safe   # to_html_safe against the cmark CLI without --unsafe
python3 markdown/gen.py                  # rewrite entities.bend from Python's html.entities
```

`conformance.py` downloads `spec.json` for 0.31.2 and checks all 652 examples byte for byte. With `--safe`, it compares `to_html_safe` with cmark 0.31.2 on the same 652 inputs; all match. `LAWS.bend` holds 25 spec examples, 8 escaping laws, and 7 safe-mode laws. Two laws hold for every string: the text escape `esc` leaves no `<`, `>`, or `"`, and each `&` it writes starts `&amp;`, `&lt;`, `&gt;`, or `&quot;`.

`bench/README.md` compares `to_html` with cmark and libraries in Rust, JavaScript, and Python.
