;; One machine combines array-backed structs, native arithmetic, exception payloads,
;; mutable globals, ordinary/reference/tail host calls, and state across actions.
(module
  (type $s (struct (field (mut i32))))
  (type $print-type (func (param i32)))
  (import "spectest" "print_i32" (func $print (type $print-type)))
  (elem declare func $print)
  (tag $e (param (ref $s)))
  (global $saved (mut (ref null $s)) (ref.null $s))
  (func $make (param i32) (result (ref $s)) local.get 0 struct.new $s)
  (func (export "compute") (param i32) (result i32)
    (local (ref null $s))
    local.get 0 call $make local.tee 1 global.set $saved
    block $out (result (ref $s))
      try_table (catch $e $out)
        local.get 1 ref.as_non_null throw $e
      end
      unreachable
    end
    struct.get $s 0
    f32.const 1.5 f32.const 2.0 f32.add i32.trunc_f32_s i32.add
    local.tee 0 local.get 0 call $print)
  (func (export "read") (result i32)
    global.get $saved ref.as_non_null struct.get $s 0)
  (func (export "mutate") (param i32)
    global.get $saved ref.as_non_null local.get 0 struct.set $s 0)
  (func (export "tail-print") (param i32)
    block local.get 0 return_call $print end)
  (func (export "ref-print") (param i32)
    local.get 0 ref.func $print call_ref $print-type))
(assert_return (invoke "compute" (i32.const 7)) (i32.const 10))
(assert_return (invoke "read") (i32.const 7))
(assert_return (invoke "compute" (i32.const 20)) (i32.const 23))
(assert_return (invoke "read") (i32.const 20))
(assert_return (invoke "mutate" (i32.const 31)))
(assert_return (invoke "read") (i32.const 31))
(assert_return (invoke "tail-print" (i32.const 99)))
(assert_return (invoke "ref-print" (i32.const 42)))
