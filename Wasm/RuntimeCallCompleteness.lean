import Wasm.Runtime
import Wasm.RuntimeMatchingCompleteness
import Wasm.RuntimeNominalShape
import Wasm.RuntimeExpectedTypesInvariant

/-! Declarative prerequisites for invocation completeness. -/
namespace Wasm

/-- Every stored function has independently valid parameter types. -/
def Store.FunctionParametersValid (store : Store) : Prop :=
  ∀ function ∈ store.funcs, ∀ type ∈ function.type.params,
    Types.RuntimeValValid {} (Types.embedVal type)

theorem Invokes.args_typed (invoked : Invokes store function args activation) :
    ArgsTyped store args function.type.params := by
  cases invoked with
  | wasm _ typed => exact typed

/-- Invocation argument search succeeds at its unchanged matching budget. -/
theorem FuncInst.activation?_complete_runtime
    (invoked : Invokes store function args activation) (valid : store.RuntimeTypesValid)
    (parameters : ∀ type ∈ function.type.params, Types.RuntimeValValid {} (Types.embedVal type)) :
    function.activation? args store = some activation :=
  function.activation?_complete invoked (checkArgs_complete valid parameters invoked.args_typed)

/-- Runtime nominal function subtyping preserves the argument count used by the scanner. -/
theorem Invokes.defined_arity {type : Types.DefinedType} {signature : Types.FuncType}
    (invoked : Invokes store function args activation)
    (found : store.func? address = some function) (valid : store.RuntimeTypesValid)
    (matched : Types.HeapMatches {} function.runtimeType.heap type.heap)
    (expanded : type.expand? = some signature) : args.length = signature.params.length := by
  have actual := valid.functions function (List.mem_of_getElem? found)
  have counts := matched.function_arity actual.1.2 actual.2 expanded
  have argsLength := invoked.args_typed.length
  have params : function.type.params.length = signature.params.length := by
    simpa only [Types.embedFunc, List.length_map] using counts.1
  exact argsLength.trans params

theorem FuncType.defined_shape (type : FuncType) :
    type.definedType.shape? = some (.func type.params.length type.results.length) := by
  simp [FuncType.definedType, Types.DefinedType.shape?, Types.DefinedType.unroll?,
    Types.RecType.unroll, Types.embedFunc, Types.FuncType.sub, Types.SubType.mapHeap,
    Types.SubType.body, Types.CompType.shape]

theorem Invokes.legacy_arity {signature : FuncType} (invoked : Invokes store function args activation)
    (found : store.func? address = some function) (valid : store.RuntimeTypesValid)
    (matched : Types.HeapMatches {} function.runtimeType.heap signature.definedType.heap) :
    args.length = signature.params.length := by
  have actual := valid.functions function (List.mem_of_getElem? found)
  have tree := (actual.1.2.runtime_nominal_shape_tree rfl).2 function.runtimeType rfl
  obtain ⟨_, path⟩ := matched.normalize_defined_tree tree.nominal
  have shapes := path.shape_eq tree
  rw [Types.DefinedType.shape_of_expand actual.2, signature.defined_shape] at shapes
  have counts := Types.CompShape.func.inj (Option.some.inj shapes)
  have params : function.type.params.length = signature.params.length := by
    simpa only [Types.embedFunc, List.length_map] using counts.1
  exact invoked.args_typed.length.trans params

#print axioms FuncInst.activation?_complete_runtime
#print axioms Invokes.defined_arity
#print axioms Invokes.legacy_arity
end Wasm
