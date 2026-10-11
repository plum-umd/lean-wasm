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

private def whitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def delimiter (c : Char) : Bool := whitespace c || c == '(' || c == ')' || c == '"'

private partial def comment (depth : Nat) : List Char → Except String (List Char)
  | [] => .error "unterminated block comment"
  | '(' :: ';' :: cs => comment (depth + 1) cs
  | ';' :: ')' :: cs => if depth == 1 then .ok cs else comment (depth - 1) cs
  | _ :: cs => comment depth cs

private partial def skip : List Char → Except String (List Char)
  | ';' :: ';' :: cs => skip (cs.dropWhile (fun c => c != '\n' && c != '\r'))
  | '(' :: ';' :: cs => do skip (← comment 1 cs)
  | c :: cs => if whitespace c then skip cs else .ok (c :: cs)
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

private partial def tokenChars (annotation : Bool) : List Char → List Char
  | [] => []
  | ';' :: ';' :: _ => []
  | c :: cs => if delimiter c || (!annotation && c == ';') then []
    else c :: tokenChars annotation cs

private def separated : List Char → Bool
  | [] => true
  | ';' :: ';' :: _ => true
  | c :: _ => whitespace c || c == '(' || c == ')'

private partial def expressions (nested annotation : Bool) (input : List Char) :
    Except String (List SExpr × List Char) := do
  let cs ← skip input
  match cs with
  | [] => if nested then .error "unclosed parenthesis" else .ok ([], [])
  | ')' :: rest => if nested then .ok ([], rest) else .error "unexpected closing parenthesis"
  | '(' :: rest =>
    let ignored := match rest with | '@' :: _ => true | _ => false
    let (items, rest) ← expressions true (annotation || ignored) rest
    if ignored && !annotation then
      match items.head? with
      | some (.atom id) => if id == "@" then throw "empty annotation identifier"
      | _ => throw "invalid annotation identifier"
    let (tail, rest) ← expressions nested annotation rest
    return (if ignored then tail else .list items :: tail, rest)
  | '"' :: rest =>
    let (bytes, rest) ← quoted {} rest
    if !annotation && !separated rest then throw "missing token separator"
    let (tail, rest) ← expressions nested annotation rest
    return (.string bytes :: tail, rest)
  | marker :: '"' :: rest =>
    if marker != '$' && marker != '@' then
      if !annotation then throw "invalid quoted token"
      let (tail, rest) ← expressions nested annotation ('"' :: rest)
      return (.atom (String.singleton marker) :: tail, rest)
    let (bytes, rest) ← quoted {} rest
    let some decoded := String.fromUTF8? bytes | throw "identifier is not UTF-8"
    if marker == '$' && decoded.isEmpty then throw "empty identifier"
    if !annotation && !separated rest then throw "missing token separator"
    let (tail, rest) ← expressions nested annotation rest
    return (.atom (String.singleton marker ++ decoded) :: tail, rest)
  | _ =>
    let token := tokenChars annotation cs
    if token.isEmpty then throw "empty token"
    if token.any (fun c => c.toNat < 32 || c.toNat ≥ 127) then throw "illegal character"
    let atom := String.ofList token
    if !annotation && atom == "$" then throw "empty identifier"
    let rest := cs.drop token.length
    if !annotation && (match rest with | '"' :: _ => true | _ => false) then
      throw "missing token separator"
    let (tail, rest) ← expressions nested annotation rest
    return (.atom atom :: tail, rest)

/-- Generic text-script reader. It preserves quoted strings as bytes. -/
def parse (text : String) : Except String (List SExpr) :=
  (expressions false false text.toList).map Prod.fst

end Wasm.Text
