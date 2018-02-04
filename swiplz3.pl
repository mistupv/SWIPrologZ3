:- module(swiplz3, [z3_mk_config/0,z3_set_param_value/2,z3_mk_context/1,z3_mk_solver/1,z3_del_config/0,z3_del_solver/1,z3_del_context/1,z3_push/1,z3_pop/1,z3_assert_string/2,z3_intconstr2smtlib/5,z3_check/1,z3_mk_int_vars/2,z3_print_model/1,get_context_vars/2,get_model_var_eval/3,constr2smt/2]).

:- use_foreign_library(swiplz3).

z3_mk_context(N) :-
    z3_mk_new_context(N),
    retractall(var(N,_)).

:- dynamic var/2.

/*
   get_varnames/2 takes a list of variables produced by numbervars
   and returns a list of strings
*/
get_varnames([],[]).
get_varnames([V|VR],[VN|VRN]) :-
    write_to_chars(V,VN_),
    string_codes(VN,VN_),
    get_varnames(VR,VRN).

/*
    intconstr2smtlib/5 takes a context, the constraints so far, a new constraint
    (over integers) and returns a list of strings with the names of the new variables
    and a string with the SMTLIB2 representation "(assert ... )"
*/

z3_intconstr2smtlib(Context,OldC,C,NewVarsStr,SMT) :-
    copy_term((OldC,C),(OldCC,CC)),
    term_variables(OldCC,OldCCVars),
    term_variables(CC,CCVars),
    numbervars((OldCCVars,CCVars)),
    subtract(CCVars,OldCCVars,NewVars),
    get_varnames(NewVars,NewVarsStr),
    (NewVarsStr=[] -> true
    ;
      assert_vars(Context,NewVarsStr)
    ),
    constr2smt(CC,SMT_),
    string_codes(SMT,SMT_),!.

/*
    z3_assert_string/2 takes an SMT formula and asserts it to a context
*/

z3_assert_string(N,SMT) :-
    string_codes(SMT,SMTC),
    string_codes("(assert ",S1),
    string_codes(" )",S2),
    append(S1,SMTC,S3),
    append(S3,S2,SMTLIB2_),
    string_codes(SMTLIB2,SMTLIB2_),
    z3_assert_string_(N,SMTLIB2).


assert_vars(_,[]).
assert_vars(N,[X|R]) :-
    assertz(var(N,X)),
    assert_vars(N,R).

get_context_vars(N,VVS) :-
    findall(VV,var(N,VV),VVS).

get_model_var_eval(_N,[],[]) :- !.
get_model_var_eval(N,[Var|R],[Val|RR]) :-
    z3_get_model_intvar_eval(N,Var,Val),
    get_model_var_eval(N,R,RR).

var_decl([],[]).
var_decl([V|R],SS) :-
    string_codes("(declare-const ",S1),
    write_to_chars(V,Var),
    append(S1,Var,S2),
    string_codes(" Int) ",S3),
    append(S2,S3,S),
    var_decl(R,RS),
    append(S,RS,SS).

/*
z3_solver_assert_int(N,C) :-
    term_variables(C,CVars),
    numbervars(CVars),get_varnames(CVars,CVarsNames)
    mk_int_var_list(N,CVarsNames),
    clp2smt(C,SMT),!,
    append([40,97,115,115,101,114,116,32|SMT],[41], SMT1), %(assert SMT)
    string_codes(SMT2,SMT1),
    z3_assert_string(N,SMT2).
*/

/*
    constr2smt/2 translates a list of simple integer constraints (>,<,=,\=,>=,=< and +,-,*,div,mod,rem)
    to a list of codes representing an SMTLIB2 string
*/

constr2smt([C],SMT) :-
    !,con2smt(C,SMT).
constr2smt(List,SMT) :-
    con2smt_list(List,SMT_),
    string_codes("(and ",S1),
    append(S1,SMT_,S2),
    string_codes(")",S3),
    append(S2,S3,SMT).

con2smt_list([C],SMT) :-
    !,con2smt(C,SMT).
con2smt_list([C|R],SMT) :-
    con2smt(C,SMT1),
    con2smt_list(R,SMTR),
    string_codes(" ",Blank),
    append(SMT1,Blank,S),
    append(S,SMTR,SMT).

/* expression rooted by a binary operator */
con2smt(T,SMT) :-
    functor(T,F,2),!,transf(F,S1,S2),
    arg(1,T,Arg1),con2smt(Arg1,SMT1),
    arg(2,T,Arg2),con2smt(Arg2,SMT2),
    string_codes(" ",Blank),
    append(S1,SMT1,S),append(S,Blank,S_),
    append(S_,SMT2,S__),append(S__,S2,SMT).

/* negative number */
con2smt(T,SMT) :-
    functor(T,-,1),!,transf(-,S1,S2),
    arg(1,T,Arg1),con2smt(Arg1,SMT1),
    append(S1,SMT1,S),append(S,S2,SMT).

/* integer */
con2smt(T,SMT) :-
    integer(T),!,
    atom_codes(T,SMT).

/* variable */
con2smt(T,SMT) :-
    functor(T,'$VAR',1),!,
    write_to_chars(T,SMT).

/* unsupported term */
con2smt(T,_SMT) :-
    throw(unsupported_constraint(T)).


/* binary operators */
transf(>,S1,S2) :- string_codes("(> ",S1),string_codes(")",S2).
transf(<,S1,S2) :- string_codes("(< ",S1),string_codes(")",S2).
transf(>=,S1,S2) :- string_codes("(>= ",S1),string_codes(")",S2).
transf(=<,S1,S2) :- string_codes("(<= ",S1),string_codes(")",S2).
transf(=,S1,S2) :- string_codes("(= ",S1),string_codes(")",S2).
transf(\=,S1,S2) :- string_codes("(not (= ",S1),string_codes("))",S2).
transf(*,S1,S2) :- string_codes("(* ",S1),string_codes(")",S2).
transf(+,S1,S2) :- string_codes("(+ ",S1),string_codes(")",S2).
transf(-,S1,S2) :- string_codes("(- ",S1),string_codes(")",S2).
transf(div,S1,S2) :- string_codes("(div ",S1),string_codes(")",S2).
transf(mod,S1,S2) :- string_codes("(mod ",S1),string_codes(")",S2).
transf(rem,S1,S2) :- string_codes("(rem ",S1),string_codes(")",S2).

/* unary operators */
transf(-,S1,S2) :- string_codes("(- ",S1),string_codes(")",S2).

