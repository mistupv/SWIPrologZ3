/* very simple example showing the functionality of the Z3 functions */

:- use_module(swiplz3).

main :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    z3_push(N),
/* first constraint */
    C1 = [X>0,X<10],
    z3_intconstr2smtlib(N,[],C1,VarsC1,C1smtlib2),
    (VarsC1=[] -> true ; z3_mk_int_vars(N,VarsC1)),
    z3_assert_string(N,C1smtlib2),
/* second constraint */
    C2 = [Y>0],
    z3_intconstr2smtlib(N,C1,C2,VarsC2,C2smtlib2),
    (VarsC2=[] -> true ; z3_mk_int_vars(N,VarsC2)),
    z3_assert_string(N,C2smtlib2),
/* third constraint */
    C3 = [X>Y],
    z3_intconstr2smtlib(N,(C1,C2),C3,VarsC3,C3smtlib2),
    (VarsC3=[] -> true ; z3_mk_int_vars(N,VarsC3)),
    z3_assert_string(N,C3smtlib2),
/* checking satisfiability */
    (z3_check(N) ->
        z3_print_model(N),
        get_context_vars(N,VVS),
        get_model_var_eval(N,VVS,Values),
        %%        nl,format("Variables: "),print(VVS),
        %%        nl,format("Values:    "),print(Values),
        term_variables((C1,C2,C3),AllVars),
        AllVars=Values,
        format("Solved formulas: "),print((C1,C2,C3)),
        nl
    ;
        true
    ),
    z3_pop(N),
    z3_del_solver(N),
    z3_del_context(N).


