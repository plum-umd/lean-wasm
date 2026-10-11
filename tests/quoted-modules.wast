(module $quoted quote
  "(func (export \"value\") (result i32)"
  " (i32.const 42))")
(assert_return (invoke $quoted "value") (i32.const 42))
(assert_invalid (module quote "(func (result i32))") "type mismatch")
(assert_malformed (module quote "(func") "unclosed parenthesis")
(assert_malformed (module quote "(func imaginary.op)") "unknown operator")
(assert_malformed (module quote "(func (if i32.const 0 (then) (else)))") "flat operand")
(assert_malformed
  (module quote "(func (type 42) (param i32))") "unknown inline signature")
(module definition $quotedDefinition quote "(func (export \"answer\") (result i32) i32.const 7)")
(module instance $quotedDefinition)
(assert_return (invoke "answer") (i32.const 7))
