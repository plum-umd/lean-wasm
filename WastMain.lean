import Wasm.Text.Script

private def options (fuel callDepth : Nat) :
    List String → Except String (Nat × Nat × List String)
  | "--fuel" :: amount :: files => do
    let some fuel := amount.toNat? | throw "--fuel requires a natural number"
    options fuel callDepth files
  | "--call-depth" :: amount :: files => do
    let some callDepth := amount.toNat? | throw "--call-depth requires a natural number"
    options fuel callDepth files
  | ["--fuel"] => .error "--fuel requires a natural number"
  | ["--call-depth"] => .error "--call-depth requires a natural number"
  | files => .ok (fuel, callDepth, files)

/-- Unsupported commands produce exit 2, failures exit 1, complete success exit 0. -/
def main (args : List String) : IO UInt32 := do
  let (fuel, callDepth, args) ← match options 10000 1024 args with
    | .ok parsed => pure parsed
    | .error message => IO.eprintln message; return 1
  if args.isEmpty then
    IO.eprintln "usage: lake exe wast [--fuel STEPS] [--call-depth FRAMES] FILE.wast ..."
    return 1
  let mut failed := false
  let mut unsupported := false
  for path in args do
    try
      let source ← IO.FS.readFile path
      match Wasm.Text.parse source with
      | .error msg =>
        IO.eprintln s!"{path}: parse error: {msg}"
        failed := true
      | .ok commands =>
        let report := Wasm.Text.runScript commands fuel callDepth
        for value in report.output do
          match value with
          | .i32 bits => IO.println s!"{bits.toInt} : i32"
          | .i64 bits => IO.println s!"{bits.toInt} : i64"
          | .f32 bits => IO.println s!"{Float32.ofBits bits.toNat.toUInt32} : f32"
          | .f64 bits => IO.println s!"{Float.ofBits bits.toNat.toUInt64} : f64"
          | .v128 bits => IO.println s!"{bits.toNat} : v128"
          | .ref _ => pure ()
        IO.println s!"{path}: {report.passed} passed, {report.failed} failed, \
          {report.unsupported} unsupported"
        for (outcome, i) in report.outcomes.zipIdx do
          if let .failed message := outcome then
            IO.eprintln s!"  {path}: command {i+1}: {message}"
        let reasons := report.outcomes.filterMap fun
          | .unsupported msg => some msg
          | _ => none
        for reason in reasons.eraseDups do
          IO.println s!"  unsupported ({reasons.count reason}): {reason}"
        failed := failed || report.failed > 0
        unsupported := unsupported || report.unsupported > 0
    catch e =>
      IO.eprintln s!"{path}: {e}"
      failed := true
  return if failed then 1 else if unsupported then 2 else 0
