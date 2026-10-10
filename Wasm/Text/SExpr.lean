import Std

namespace Wasm.Text

inductive SExpr where
  | atom (text : String)
  | string (bytes : ByteArray)
  | list (items : List SExpr)
  deriving BEq

private def hex (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def delimiter (c : Char) : Bool := c.isWhitespace || c == '(' || c == ')' || c == '"'

private partial def comment (depth : Nat) : List Char → Except String (List Char)
  | [] => .error "unterminated block comment"
  | '(' :: ';' :: cs => comment (depth + 1) cs
  | ';' :: ')' :: cs => if depth == 1 then .ok cs else comment (depth - 1) cs
  | _ :: cs => comment depth cs

private partial def skip : List Char → Except String (List Char)
  | ';' :: ';' :: cs => skip (cs.dropWhile (· != '\n'))
  | '(' :: ';' :: cs => do skip (← comment 1 cs)
  | c :: cs => if c.isWhitespace then skip cs else .ok (c :: cs)
  | [] => .ok []

private def unicodeEscape (cs : List Char) : Except String (Char × List Char) := do
  let '{' :: cs := cs | throw "expected brace in Unicode escape"
  let digits := cs.takeWhile (· != '}')
  let '}' :: rest := cs.drop digits.length | throw "unterminated Unicode escape"
  if digits.isEmpty then throw "empty Unicode escape"
  let mut n := 0
  for c in digits do
    let some d := hex c | throw "invalid Unicode escape"
    n := 16 * n + d
    if n > 0x10ffff then throw "Unicode escape out of range"
  if 0xd800 ≤ n && n ≤ 0xdfff then throw "Unicode surrogate escape"
  return (Char.ofNat n, rest)

private partial def quoted (out : ByteArray) : List Char →
    Except String (ByteArray × List Char)
  | [] => .error "unterminated string"
  | '"' :: cs => .ok (out, cs)
  | '\\' :: a :: b :: cs =>
    match hex a, hex b with
    | some x, some y => quoted (out.push (UInt8.ofNat (16*x+y))) cs
    | _, _ => escaped out a (b :: cs)
  | '\\' :: a :: cs => escaped out a cs
  | c :: cs =>
    if c.toNat < 32 || c.toNat == 127 || c == '\\' then .error "invalid string character"
    else quoted (out ++ (String.singleton c).toUTF8) cs
where
  escaped (out : ByteArray) (c : Char) (cs : List Char) :=
    match c with
    | 'u' => do
      let (scalar, rest) ← unicodeEscape cs
      quoted (out ++ (String.singleton scalar).toUTF8) rest
    | '\'' => quoted (out.push 39) cs
    | 'n' => quoted (out.push 10) cs
    | 'r' => quoted (out.push 13) cs
    | 't' => quoted (out.push 9) cs
    | '"' => quoted (out.push 34) cs
    | '\\' => quoted (out.push 92) cs
    | _ => .error "unsupported or invalid string escape"

private partial def expressions (nested : Bool) (input : List Char) :
    Except String (List SExpr × List Char) := do
  let cs ← skip input
  match cs with
  | [] => if nested then .error "unclosed parenthesis" else .ok ([], [])
  | ')' :: rest => if nested then .ok ([], rest) else .error "unexpected closing parenthesis"
  | '(' :: rest =>
    let (items, rest) ← expressions true rest
    let (tail, rest) ← expressions nested rest
    return (.list items :: tail, rest)
  | '"' :: rest =>
    let (bytes, rest) ← quoted {} rest
    let (tail, rest) ← expressions nested rest
    return (.string bytes :: tail, rest)
  | _ =>
    let token := cs.takeWhile (!delimiter ·)
    if token.isEmpty then throw "empty token"
    let (tail, rest) ← expressions nested (cs.drop token.length)
    return (.atom (String.ofList token) :: tail, rest)

/-- Generic text-script reader. It preserves quoted strings as bytes. -/
def parse (text : String) : Except String (List SExpr) :=
  (expressions false text.toList).map Prod.fst

end Wasm.Text
