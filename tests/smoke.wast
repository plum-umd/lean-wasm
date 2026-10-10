;; A fully supported script for the initial integer frontend.
(module $integers
  (func $identity (param $x i32) (result i32) local.get $x)
  (func (export "twice") (param $x i32) (result i32) (local $saved i32)
    (local.set $saved (call $identity (local.get $x)))
    (i32.add (local.get $saved) (local.tee $saved (local.get $x))))
  (func (export "trap") unreachable))
(assert_return (invoke "twice" (i32.const 21)) (i32.const 42))
(assert_return (invoke $integers "twice" (i32.const 0xffffffff)) (i32.const -2))
(assert_trap (invoke "trap") "unreachable")
