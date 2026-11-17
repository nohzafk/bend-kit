# Paragraph scaling benchmark: to_html time on one paragraph of N lines (see README.md).
import Base
import ../../time/time.bend as Time
import ../markdown.bend as M

def line(+link: Bool) -> String:
  "Some *emphasis*, **strong**, `code <tag>`, " ++ Bool.pick(String, link, "a [link](https://example.com/?a=1 \"title\"), ", "") ++ "and &amp; text.\n"

def para(n: Nat, +link: Bool) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      line(link) ++ para(p, link)

def time(+n: Nat, +link: Bool) -> IO(Unit):
  do IO<Unit>:
    +d : String = para(n, link)
    t0 : Time.Duration <- Time.mono()
    len : Nat = String.length(M.to_html(d))
    t1 : Time.Duration <- Time.mono()
    IO.print(Bool.pick(String, link, "links", "plain") ++ "\t" ++ Nat.show(n) ++ "\t" ++ Nat.show(len) ++ "\t" ++ Time.Duration.show_ms(Time.Duration.sub(t1, t0)))

def main() -> IO(Unit):
  do IO<Unit>:
    time(100n, True{})
    time(200n, True{})
    time(400n, True{})
    time(800n, True{})
    time(1600n, True{})
    time(100n, False{})
    time(200n, False{})
    time(400n, False{})
    time(800n, False{})
    time(1600n, False{})
