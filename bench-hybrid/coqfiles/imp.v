Require Import Minuska.pval_ocaml_binding Minuska.builtin.klike Minuska.pi.trivial Minuska.default_everything.
Definition mysignature := (bi_signature MyUnit builtins_klike).
#[global] Existing Instance mysignature.
Definition mybeta := (bi_beta MyUnit builtins_klike).
#[global] Existing Instance mybeta.
Definition my_program_info := trivial.MyProgramInfo.
Definition mysigma : StaticModel := (default_everything.DSM my_program_info).
Existing Instance mysigma.
#[global] Existing Instance my_program_info.
Definition myContext := (context-template (@t_term _ _ "c" [(HOLE); (t_over (notations.inject_variable "STATE"))]) with HOLE).
Definition isValue (X : Expression2) := (sc_or (sc_atom b_isZ [(X)])(sc_or (sc_atom b_isString [(X)])(sc_or (sc_atom b_isBool [(X)])(sc_atom b_have_same_symbol [(X); (e_ground (@t_term symbol builtin_value "unitValue" []))])))).
#[export] Instance isValue_nsc (X : Expression2) : NegableSideCondition (isValue X) := ltac:(intros; unfold isValue in *; apply _).


#[local]
Instance LangDefaults : Defaults := {|
    default_cseq_name := "builtin.cseq" ;
    default_empty_cseq_name := "builtin.empty_cseq" ;
    default_context_template := myContext ;

    default_isValue := isValue ;
|}.

Definition frame_simple : (variable*(TermOver BuiltinOrVar)) := ("X",(@t_term symbol BuiltinOrVar "c" [(@t_term symbol BuiltinOrVar "builtin.cseq" [(t_over (bov_variable "X")); (t_over (bov_variable "REST"))]); (t_over (bov_variable "STATE"))])).
Definition Lang_Decls : list Declaration := [
(decl_strict (mkStrictnessDeclaration _ "plus" 2 [0; 1] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "minus" 2 [0; 1] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "assign" 2 [1] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "seq" 2 [0] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "ite" 3 [0] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "eq" 2 [0; 1] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "le" 2 [0; 1] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "lt" 2 [0; 1] isValue _ myContext))
;(decl_strict (mkStrictnessDeclaration _ "neg" 1 [0] isValue _ myContext))
] ++ [
(basic_rule my_program_info "init" (@t_term symbol BuiltinOrVar "builtin.init" []) (@t_term symbol Expression2 "c" [(@t_term symbol Expression2 "builtin.cseq" [(@t_over symbol Expression2(e_query qs_program [])); (@t_term symbol Expression2 "builtin.empty_cseq" [])]); (@t_over symbol Expression2(e_fun b_map_empty []))]) sc_true)
; (framed_rule my_program_info frame_simple "aexpr.plus" (@t_term symbol BuiltinOrVar "plus" [(t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_fun b_Z_plus [(e_variable "X"); (e_variable "Y")])) (sc_and (sc_atom b_isZ [(e_variable "X")])(sc_atom b_isZ [(e_variable "Y")])))
; (framed_rule my_program_info frame_simple "aexpr.minus" (@t_term symbol BuiltinOrVar "minus" [(t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_fun b_Z_minus [(e_variable "X"); (e_variable "Y")])) (sc_and (sc_atom b_isZ [(e_variable "X")])(sc_atom b_isZ [(e_variable "Y")])))
; (basic_rule my_program_info "var.assign" (@t_term symbol BuiltinOrVar "c" [(@t_term symbol BuiltinOrVar "builtin.cseq" [(@t_term symbol BuiltinOrVar "assign" [(t_over (bov_variable "X")); (t_over (bov_variable "V"))]); (t_over (bov_variable "REST"))]); (t_over (bov_variable "STATE"))]) (@t_term symbol Expression2 "c" [(@t_term symbol Expression2 "builtin.cseq" [(@t_term symbol Expression2 "unitValue" []); (@t_over symbol Expression2(e_variable "REST"))]); (@t_over symbol Expression2(e_fun b_map_update [(e_variable "STATE"); (e_variable "X"); (e_variable "V")]))]) (sc_and (sc_atom b_have_same_symbol [(e_variable "X"); (e_ground (@t_term symbol builtin_value "var" []))])(sc_or (sc_atom b_isZ [(e_variable "V")])(sc_atom b_isString [(e_variable "V")]))))
; (basic_rule my_program_info "var.lookup" (@t_term symbol BuiltinOrVar "c" [(@t_term symbol BuiltinOrVar "builtin.cseq" [(t_over (bov_variable "X")); (t_over (bov_variable "REST"))]); (t_over (bov_variable "STATE"))]) (@t_term symbol Expression2 "c" [(@t_term symbol Expression2 "builtin.cseq" [(@t_over symbol Expression2(e_fun b_map_lookup [(e_variable "STATE"); (e_variable "X")])); (@t_over symbol Expression2(e_variable "REST"))]); (@t_over symbol Expression2(e_variable "STATE"))]) (sc_atom b_have_same_symbol [(e_variable "X"); (e_ground (@t_term symbol builtin_value "var" []))]))
; (framed_rule my_program_info frame_simple "stmt.seq" (@t_term symbol BuiltinOrVar "seq" [(@t_term symbol BuiltinOrVar "unitValue" []); (t_over (bov_variable "X"))]) (@t_over symbol Expression2(e_variable "X")) sc_true)
; (framed_rule my_program_info frame_simple "bexpr.eq" (@t_term symbol BuiltinOrVar "eq" [(t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_fun b_Z_eq [(e_variable "X"); (e_variable "Y")])) (sc_and (sc_atom b_isZ [(e_variable "X")])(sc_atom b_isZ [(e_variable "Y")])))
; (framed_rule my_program_info frame_simple "bexpr.le" (@t_term symbol BuiltinOrVar "le" [(t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_fun b_Z_isLe [(e_variable "X"); (e_variable "Y")])) (sc_and (sc_atom b_isZ [(e_variable "X")])(sc_atom b_isZ [(e_variable "Y")])))
; (framed_rule my_program_info frame_simple "bexpr.lt" (@t_term symbol BuiltinOrVar "lt" [(t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_fun b_Z_isLt [(e_variable "X"); (e_variable "Y")])) (sc_and (sc_atom b_isZ [(e_variable "X")])(sc_atom b_isZ [(e_variable "Y")])))
; (framed_rule my_program_info frame_simple "bexpr.neg" (@t_term symbol BuiltinOrVar "not" [(t_over (bov_variable "X"))]) (@t_over symbol Expression2(e_fun b_bool_neg [(e_variable "X")])) (sc_atom b_isBool [(e_variable "X")]))
; (framed_rule my_program_info frame_simple "stmt.ite.true" (@t_term symbol BuiltinOrVar "ite" [(t_over (bov_variable "B")); (t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_variable "X")) (sc_and (sc_atom b_isBool [(e_variable "B")])(sc_atom b_bool_is_true [(e_variable "B")])))
; (framed_rule my_program_info frame_simple "stmt.ite.false" (@t_term symbol BuiltinOrVar "ite" [(t_over (bov_variable "B")); (t_over (bov_variable "X")); (t_over (bov_variable "Y"))]) (@t_over symbol Expression2(e_variable "Y")) (sc_and (sc_atom b_isBool [(e_variable "B")])(sc_atom b_bool_is_false [(e_variable "B")])))
; (framed_rule my_program_info frame_simple "while.unfold" (@t_term symbol BuiltinOrVar "while" [(t_over (bov_variable "B")); (t_over (bov_variable "S"))]) (@t_term symbol Expression2 "ite" [(@t_over symbol Expression2(e_variable "B")); (@t_term symbol Expression2 "seq" [(@t_over symbol Expression2(e_variable "S")); (@t_term symbol Expression2 "while" [(@t_over symbol Expression2(e_variable "B")); (@t_over symbol Expression2(e_variable "S"))])]); (@t_term symbol Expression2 "unitValue" [])]) sc_true)

].
Definition T := Eval vm_compute in (to_theory Act (process_declarations Act default_act mysignature mybeta my_program_info Lang_Decls)). 
Definition lang_interpreter (*: (StepT my_program_info)*) := global_naive_interpreter my_program_info (fst T).
Definition lang_interpreter_ext (*: (StepT_ext my_program_info)*) := global_naive_interpreter_ext my_program_info (fst T).
Definition lang_debug_info : list string := (snd T).

    (* This lemma asserts well-formedness of the definition *)
    Lemma language_well_formed: isSome(RewritingTheory2_wf_heuristics (fst T)).
    Proof.
      (* This is the main syntactic check. If this fails, the semantics contain a bad rule. *) ltac1:(compute_done).
    Qed.
    (* This lemma asserts soundness of the generated interpreter. *)
    (* Unfortunately, we cannot rely on the extraction here.
    Lemma interp_sound:
        Interpreter_sound'
        (fst T)
        lang_interpreter
    .
    Proof.
        apply @global_naive_interpreter_sound.
        (*{ apply _. }*)
        ltac1:(assert(Htmp: isSome(RewritingTheory2_wf_heuristics (fst T)))).
        {
            apply language_well_formed.
        }
        unfold is_true, isSome in Htmp.
        destruct (RewritingTheory2_wf_heuristics (fst T)) eqn:Heq>[|inversion Htmp].
        assumption.
    Qed.
    *)
  
Definition chosen_builtins := builtins_klike.
