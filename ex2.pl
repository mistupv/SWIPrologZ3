/* a very simple clp interpreter over integers using the Z3 SMT solver */

:- use_module(swiplz3).

:- dynamic context/1.

init :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    assert(context(N)),
    z3_mk_solver(N),
    z3_del_config.

solve(true,C,C).
solve((A,B),C,CB):-
    solve(A,C,CA),solve(B,CA,CB).
solve(A,C,CA):-
    clp_clause(A,[],B),
    solve(B,C,CA).
solve(A,C,CC):-
    clp_clause(A,CA,B),CA\=[],
    /* constraint solving using Z3 */
    context(N),
    z3_intconstr2smtlib(N,C,CA,VarsC,Csmtlib2),
    (VarsC=[] -> true ; z3_mk_int_vars(N,VarsC)),
    z3_assert_string(N,Csmtlib2),z3_check(N),
    /* end */
    append(C,CA,CC_),
    solve(B,CC_,CC).


/* a concrete example */

clp_clause(list_length([],Length),[Length=0],true).
clp_clause(list_length([_|Ls], Length),[Length = Length0 + 1],list_length(Ls, Length0)).

/* you can test a goal using solve/1 */

solve(G) :-
    init,
    solve(G,[],C),
    /* producing a solution */
    context(N),
    get_context_vars(N,VVS),
    get_model_var_eval(N,VVS,Values),
    term_variables(C,AllVars),
    AllVars=Values.

/*
    try, e.g., ?- solve(list_length([1,2,3],L)).
*/

