(module (func (drop (ref.is_null (select (unreachable) (i32.const 1))))))
(module
  (func (export "trap") (result i64)
    unreachable i64.const 7 i32.const 1 select))
(assert_trap (invoke "trap") "unreachable")
(assert_invalid
  (module (func unreachable ref.null func i32.const 1 select drop))
  "known reference operand")
(assert_invalid
  (module (func i32.const 1 select ref.is_null drop))
  "reachable underflow")
