import Wasm.Text.Script

/-- Unsupported commands produce exit 2, failures exit 1, complete success exit 0. -/
def main (args : List String) : IO UInt32 := do
  let (fuel, args) ← match args with
    | "--fuel" :: amount :: files =>
      match amount.toNat? with
      | some fuel => pure (fuel, files)
      | none => IO.eprintln "--fuel requires a natural number"; return 1
    | _ => pure (10000, args)
  if args.isEmpty then
    IO.eprintln "usage: lake exe wast [--fuel STEPS] FILE.wast ..."
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
        let report := Wasm.Text.runScript commands fuel
        for value in report.output do
          match value with
          | .i32 bits => IO.println s!"{bits.toInt} : i32"
          | .i64 bits => IO.println s!"{bits.toInt} : i64"
          | .f32 bits => IO.println s!"{Float32.ofBits bits.toNat.toUInt32} : f32"
          | .f64 bits => IO.println s!"{Float.ofBits bits.toNat.toUInt64} : f64"
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
