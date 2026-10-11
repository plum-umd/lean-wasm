(module
  (func $recurse (export "direct") (call $recurse))
  (type $void (func))
  (table 1 funcref)
  (elem (i32.const 0) $indirect)
  (func $indirect (export "indirect")
    (call_indirect (type $void) (i32.const 0)))
  (func (export "shallow") (block (loop nop))))
(assert_exhaustion (invoke "direct") "call stack exhausted")
(assert_exhaustion (invoke "indirect") "call stack exhausted")
(assert_return (invoke "shallow"))

(module
  (type $void (func))
  (func $recurse (export "reference") (type $void) ref.func $recurse call_ref $void)
  (elem declare func $recurse))
(assert_exhaustion (invoke "reference") "call stack exhausted")
