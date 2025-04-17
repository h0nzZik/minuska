From Minuska Require Import
  prelude
  default_everything
  pval_ocaml_binding
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
| ps_is_z
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
| fs_z_plus (* Z -> Z -> Z*)
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


#[local]
Obligation Tactic := idtac.


#[export]
Program Instance FunctionSymbol_fin : Finite FunctionSymbol := {|
    enum := [
  fs_bool_neg (* bool -> bool *)
; fs_stack_head (* Stack -> StackFrame *)
; fs_stack_tail (* Stack -> Stack *)
; fs_stack_push (* Stack -> StackFrame -> Stack *)
; fs_frame_has (* StackFrame -> Identifier -> bool *)
; fs_frame_lookup (* StackFrame -> Identifier -> Value *)
; fs_frame_insert (* StackFrame -> Identifier -> Value -> StackFrame *)
; fs_frame_delete (* StackFrame -> Identifier -> StackFrame *)
; fs_z_plus (* Z -> Z -> Z*)

    ]
|}.
Next Obligation.
    (* This is probably not the fastest way but it works. *)
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    intros x; destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

#[export]
Program Instance PredicateSymbol_fin : Finite PredicateSymbol := {|
    enum := [
  ps_is_value
; ps_is_stack
; ps_is_z
; ps_stack_is_empty
; ps_stack_is_nonempty
; ps_bool_is_true
; ps_bool_is_false
    ]
|}.
Next Obligation.
    (* This is probably not the fastest way but it works. *)
    (repeat constructor); ltac1:(set_solver).
Qed.
Next Obligation.
    intros x; destruct x; ltac1:(set_solver).
Qed.
Fail Next Obligation.

#[local]
    Program Instance mysignature : Signature := {|
        builtin_function_symbol
            := FunctionSymbol ;

        builtin_predicate_symbol
            := PredicateSymbol ;
    
        bps_ar := fun p =>
            match p with
            | ps_is_value => 1
            | ps_is_stack => 1
            | ps_is_z => 1
            | ps_stack_is_empty => 1
            | ps_stack_is_nonempty => 1
            | ps_bool_is_true => 1
            | ps_bool_is_false => 1
            end ;
        bps_neg := fun p =>
            match p with
            | ps_is_value => None
            | ps_is_stack => None
            | ps_is_z => None
            | ps_stack_is_empty => Some ps_stack_is_nonempty
            | ps_stack_is_nonempty => Some ps_stack_is_empty
            | ps_bool_is_true => Some ps_bool_is_false
            | ps_bool_is_false => Some ps_bool_is_true
            end ;

    |}.
    Next Obligation.
        intros p p' H; destruct p, p'; ltac1:(simplify_eq/=); reflexivity.
    Qed.
    Next Obligation.
        intros p p' H; destruct p; simpl; ltac1:(simplify_eq/=); try reflexivity.
    Qed.
    Fail Next Obligation.

#[local]
Obligation Tactic := Program.Tactics.program_simpl.

Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .


    #[local]
    Program Instance βover
        : ModelOver mysignature MyUnit PrimitiveValue := {|
        builtin_function_interp
            := fun
              (f : builtin_function_symbol)
              (nd : _)
              (args : list (TermOver' PrimitiveValue))
              => None
        ;

        builtin_predicate_interp
            := fun
              (p : builtin_predicate_symbol)
              (nd : _)
              (args : list (TermOver' PrimitiveValue))
              =>
              None
        ;
        bps_neg_correct := _;
        
    |}.
    Fail Next Obligation.
    
    #[local]
    Instance β
        : Model mysignature MyUnit
    := {|
        builtin_value
            := PrimitiveValue ;

        builtin_model_over := βover ;
    |}.
End sec.

Definition inject_err
    {symbol : Type}
    :
    PrimitiveValue :=
  pv_err
.


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


(* TOOO *)
Definition builtins_binding : BuiltinsBinding := {|
    bb_function_names := [
      ("z.is","ps_is_z");
      ("z.plus","fs_z_plus")
    ] ;
|}.


Definition builtins_myalg : BuiltinInterface MyUnit := {|
    bi_beta := β ;
    bi_bindings := builtins_binding ;
    bi_inject_err := @inject_err string;
    bi_inject_bool := @inject_bool string;
    bi_inject_Z := @inject_Z string;
    bi_inject_string := @inject_string string;
    bi_eject := @eject string;
|}.

Extract Inductive BuiltinInterface => "Libminuska.Extracted.builtinInterface" [ "(fun (a, b, c, d, e, f,g) -> { Libminuska.Extracted.bi_beta = a; Libminuska.Extracted.bi_bindings = b; Libminuska.Extracted.bi_inject_err = c; Libminuska.Extracted.bi_inject_bool = d; Libminuska.Extracted.bi_inject_Z = e; Libminuska.Extracted.bi_inject_string = f; Libminuska.Extracted.bi_eject = g; })" ].
Extract Inductive string => "Libminuska.Extracted.string" [ "Libminuska.Extracted.EmptyString" "Libminuska.Extracted.String" ].
Extract Inductive Signature => "Libminuska.Extracted.signature" [ "(fun (x1,x2) -> Libminuska.Extracted.builtin_function_symbol_eqdec = x1; Libminuska.Extracted.builtin_predicate_symbol_eqdec = x2; ))" ].
Extract Inductive Model => "Libminuska.Extracted.model" [  "(fun (x1,x2,x3) -> {Libminuska.Extracted.builtin_value_eqdec = x1; Libminuska.Extracted.builtin_function_interp = x2; Libminuska.Extracted.builtin_predicate_interp = x3;})" ].
Extract Inductive Ascii.ascii => "Libminuska.Extracted.ascii" [ "Libminuska.Extracted.Ascii" ].

Definition fancy_number := 5.

Extraction
  "myalgebra.ml"
   fancy_number
   builtins_myalg
.
