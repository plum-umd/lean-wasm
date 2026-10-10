;; Structured integer control: flat/folded syntax, labels, parameters, and dead code.
(module $control
  (func (export "folded") (param $c i32) (result i32)
    (if $choose (result i32) (local.get $c)
      (then (block $out (result i32) (br $out (i32.const 11)) (i32.const 99)))
      (else (i32.const 22))))
  (func (export "flat") (param $c i32) (result i32)
    local.get $c
    if $choose (result i32)
      i32.const 33
    else $choose
      i32.const 44
    end $choose)
  (func (export "countdown") (param $n i32) (result i32)
    loop $again
      local.get $n i32.const 1 i32.sub local.tee $n
      br_if $again
    end $again
    local.get $n)
  (func $pair (export "pair") (result i32 i64)
    i32.const 5
    block (param i32) (result i32 i64)
      i64.const 6
    end)
  (func (export "forward") (result i32 i64) (call $pair))
  (func (export "table") (param $selector i32) (result i32)
    (block $out (result i32)
      (br_table $out $out (i32.const 55) (local.get $selector))
      (i32.const 99)))
  (func (export "shadow") (result i32)
    (block $same (result i32)
      (block $same (result i32) (br $same (i32.const 7)) (i32.const 99))))
  (func (export "condition-branch") (result i32)
    (block $out (result i32)
      (if $inner (result i32) (br $out (i32.const 42))
        (then (i32.const 11)) (else (i32.const 22)))))
  (func (export "unknown-select") (result i64) unreachable select)
  (func (export "return") (result i32)
    (return (i32.const 66)) (i64.add) (drop)))
(assert_return (invoke "folded" (i32.const 1)) (i32.const 11))
(assert_return (invoke "folded" (i32.const 0)) (i32.const 22))
(assert_return (invoke "flat" (i32.const 1)) (i32.const 33))
(assert_return (invoke "flat" (i32.const 0)) (i32.const 44))
(assert_return (invoke "countdown" (i32.const 3)) (i32.const 0))
(assert_return (invoke "pair") (i32.const 5) (i64.const 6))
(assert_return (invoke "forward") (i32.const 5) (i64.const 6))
(assert_return (invoke "table" (i32.const 0)) (i32.const 55))
(assert_return (invoke "table" (i32.const 100)) (i32.const 55))
(assert_return (invoke "shadow") (i32.const 7))
(assert_return (invoke "condition-branch") (i32.const 42))
(assert_trap (invoke "unknown-select") "unreachable")
(assert_return (invoke "return") (i32.const 66))

;; Outer operands cannot cross a block's frame boundary.
(assert_invalid (module (func i32.const 1 (block i32.eqz drop))) "type mismatch")
(assert_invalid (module (func unreachable (block i32.add drop))) "type mismatch")
(assert_invalid (module (func i32.const 1 (if (result i32) (then i32.const 2)) drop))
  "type mismatch")
(assert_invalid (module (func (block br 2))) "unknown label")
(assert_invalid (module (func (block (result i64)
  (block (result i32) unreachable br_table 0 1)) drop)) "type mismatch")
(assert_invalid (module (func (result i64)
  i32.const 7 loop (param i32) (result i64) i64.const 9 br 0 end)) "type mismatch")
(assert_invalid (module (func unreachable i32.const 1 i64.add drop)) "type mismatch")
(assert_invalid (module (func unreachable i32.const 1)) "type mismatch")
