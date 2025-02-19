From Minuska Require Import
  prelude
  default_everything
.

(*  Oxide values *)
Inductive Value :=
| v_dead
| v_z (z : Z)
.

Definition Identifier := string.
Definition StackFrame := gmap Identifier Value.
Definition Stack := list StackFrame.

(* Minuska's values (forming a primitive-value-algebra) *)
Inductive PrimitiveValue :=
| pv_err
| pv_bool (b : bool)
| pv_z (z : Z)
| pv_ident (x : Identifier)
| pv_value (v : Value)
| pv_stackframe (f : StackFrame)
| pv_stack (s : Stack)
.


Variant PredicateSymbol :=
| ps_is_value
| ps_is_stack
| ps_stack_is_empty
| ps_stack_is_nonempty
| ps_bool_is_true
| ps_bool_is_false
.

Variant FunctionSymbol :=
| fs_bool_neg (* bool -> bool *)
| fs_stack_head (* Stack -> StackFrame *)
| fs_stack_tail (* Stack -> Stack *)
| fs_stack_push (* Stack -> StackFrame -> Stack *)
| fs_frame_has (* StackFrame -> Identifier -> bool *)
| fs_frame_lookup (* StackFrame -> Identifier -> Value *)
| fs_frame_insert (* StackFrame -> Identifier -> Value -> StackFrame *)
| fs_frame_delete (* StackFrame -> Identifier -> StackFrame *)
.


#[export]
Instance Value_eqdec : EqDecision Value.
Proof.
  ltac1:(solve_decision).
Defined.

#[export]
Instance PrimitiveValue_eqdec : EqDecision PrimitiveValue.
Proof.
  ltac1:(solve_decision).
Defined.

#[export]
Instance PredicateSymbol_eqdec : EqDecision PredicateSymbol.
Proof.
  ltac1:(solve_decision).
Defined.

#[export]
Instance FunctionSymbol_eqdec : EqDecision FunctionSymbol.
Proof.
  ltac1:(solve_decision).
Defined.

Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .


    #[local]
    Instance β
        : Builtin MyUnit := {|
        builtin_value
            := PrimitiveValue ;
        builtin_function_symbol
            := FunctionSymbol ;
        builtin_predicate_symbol
            := PredicateSymbol ;
        builtin_function_interp
            := fun
              (f : FunctionSymbol)
              (nd : _)
              (args : list (TermOver' PrimitiveValue))
              => (t_over pv_err)
        ;

        builtin_predicate_interp
            := fun
              (p : PredicateSymbol)
              (nd : _)
              (args : list (TermOver' PrimitiveValue))
              =>
              false
        ;
    |}.

End sec.

Definition builtins_binding : BuiltinsBinding := {|
    bb_function_names := [] ;
|}.

Definition inject_bool
    {symbol : Type}
    (Fret : option PrimitiveValue -> PrimitiveValue)
    (b : bool)
    :
    PrimitiveValue :=
    Fret (Some (pv_bool b))
.

Definition inject_Z
    {symbol : Type}
    (Fret : option PrimitiveValue -> PrimitiveValue)
    (z : Z)
    :
    PrimitiveValue :=
    Fret (Some (pv_z z))
.

Definition inject_string
    {symbol : Type}
    (Fret : option PrimitiveValue -> PrimitiveValue)
    (s : string)
    :
    PrimitiveValue :=
    Fret (Some (pv_ident s))
.

Definition eject
    {symbol : Type}
    (v : PrimitiveValue)
    :
    option (bool+(Z+(string+unit)))%type
  :=
    match v with
    | pv_err => Some (inr (inr (inr tt)))
    | pv_ident s => Some (inr (inr (inl s)))
    | pv_bool b => Some (inl b)
    | pv_value v' => None
    | pv_z z => Some (inr (inl z))
    | pv_stackframe _ => None
    | pv_stack _ => None
    end
.

Definition fancy_number := 5.

Extraction
  "myalgebra.ml"
   fancy_number
.
