//
//  aux.c
//  
//
//  Created by German Vidal on 24/01/2018.
//

#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>
#include <SWI-Prolog.h>

#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif

#define MAXCONS 64
#define MAXVARS 256

/* Some global variables */

Z3_config cfg;  //we consider a single configuration
Z3_context ctx[MAXCONS]; //but MAXCONS different contexts
Z3_solver z3s[MAXCONS];  //and solvers

Z3_symbol names[MAXCONS][MAXVARS];
Z3_func_decl decls[MAXCONS][MAXVARS];
int numvar[MAXCONS] = { 0 }; /* current number of variables in each context */

long cur = 0; /* current context */

/**
 \brief exit gracefully in case of error.
 */
void exitf(const char* message)
{
    fprintf(stderr,"BUG: %s.\n", message);
    exit(1);
}

/**
 \brief exit if unreachable code was reached.
 */
void unreachable()
{
    exitf("unreachable code was reached");
}


/***************************************************/
/*               some pretty printing              */
/***************************************************/

/**
 \brief Display a symbol in the given output stream.
 */
void display_symbol(Z3_context c, FILE * out, Z3_symbol s)
{
    switch (Z3_get_symbol_kind(c, s)) {
        case Z3_INT_SYMBOL:
            fprintf(out, "#%d", Z3_get_symbol_int(c, s));
            break;
        case Z3_STRING_SYMBOL:
            fprintf(out, "%s", Z3_get_symbol_string(c, s));
            break;
        default:
            unreachable();
    }
}

/**
 \brief Display the given type.
 */
void display_sort(Z3_context c, FILE * out, Z3_sort ty)
{
    switch (Z3_get_sort_kind(c, ty)) {
        case Z3_UNINTERPRETED_SORT:
            display_symbol(c, out, Z3_get_sort_name(c, ty));
            break;
        case Z3_BOOL_SORT:
            fprintf(out, "bool");
            break;
        case Z3_INT_SORT:
            fprintf(out, "int");
            break;
        case Z3_REAL_SORT:
            fprintf(out, "real");
            break;
        case Z3_BV_SORT:
            fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
            break;
        case Z3_ARRAY_SORT:
            fprintf(out, "[");
            display_sort(c, out, Z3_get_array_sort_domain(c, ty));
            fprintf(out, "->");
            display_sort(c, out, Z3_get_array_sort_range(c, ty));
            fprintf(out, "]");
            break;
        case Z3_DATATYPE_SORT:
            if (Z3_get_datatype_sort_num_constructors(c, ty) != 1)
        {
            fprintf(out, "%s", Z3_sort_to_string(c,ty));
            break;
        }
        {
            unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
            unsigned i;
            fprintf(out, "(");
            for (i = 0; i < num_fields; i++) {
                Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
                if (i > 0) {
                    fprintf(out, ", ");
                }
                display_sort(c, out, Z3_get_range(c, field));
            }
            fprintf(out, ")");
            break;
        }
        default:
            fprintf(out, "unknown[");
            display_symbol(c, out, Z3_get_sort_name(c, ty));
            fprintf(out, "]");
            break;
    }
}

/**
 \brief Custom ast pretty printer.
 
 This function demonstrates how to use the API to navigate terms.
 */
void display_ast(Z3_context c, FILE * out, Z3_ast v)
{
    switch (Z3_get_ast_kind(c, v)) {
        case Z3_NUMERAL_AST: {
            Z3_sort t;
            fprintf(out, "%s", Z3_get_numeral_string(c, v));
            t = Z3_get_sort(c, v);
            fprintf(out, ":");
            display_sort(c, out, t);
            break;
        }
        case Z3_APP_AST: {
            unsigned i;
            Z3_app app = Z3_to_app(c, v);
            unsigned num_fields = Z3_get_app_num_args(c, app);
            Z3_func_decl d = Z3_get_app_decl(c, app);
            fprintf(out, "%s", Z3_func_decl_to_string(c, d));
            if (num_fields > 0) {
                fprintf(out, "[");
                for (i = 0; i < num_fields; i++) {
                    if (i > 0) {
                        fprintf(out, ", ");
                    }
                    display_ast(c, out, Z3_get_app_arg(c, app, i));
                }
                fprintf(out, "]");
            }
            break;
        }
        case Z3_QUANTIFIER_AST: {
            fprintf(out, "quantifier");
            ;
        }
        default:
            fprintf(out, "#unknown");
    }
}

/**
 \brief Custom function interpretations pretty printer.
 */
void display_function_interpretations(Z3_context c, FILE * out, Z3_model m)
{
    unsigned num_functions, i;
    
    fprintf(out, "function interpretations:\n");
    
    num_functions = Z3_model_get_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
        Z3_func_decl fdecl;
        Z3_symbol name;
        Z3_ast func_else;
        unsigned num_entries = 0, j;
        Z3_func_interp_opt finterp;
        
        fdecl = Z3_model_get_func_decl(c, m, i);
        finterp = Z3_model_get_func_interp(c, m, fdecl);
        Z3_func_interp_inc_ref(c, finterp);
        name = Z3_get_decl_name(c, fdecl);
        display_symbol(c, out, name);
        fprintf(out, " = {");
        if (finterp)
        num_entries = Z3_func_interp_get_num_entries(c, finterp);
        for (j = 0; j < num_entries; j++) {
            unsigned num_args, k;
            Z3_func_entry fentry = Z3_func_interp_get_entry(c, finterp, j);
            Z3_func_entry_inc_ref(c, fentry);
            if (j > 0) {
                fprintf(out, ", ");
            }
            num_args = Z3_func_entry_get_num_args(c, fentry);
            fprintf(out, "(");
            for (k = 0; k < num_args; k++) {
                if (k > 0) {
                    fprintf(out, ", ");
                }
                display_ast(c, out, Z3_func_entry_get_arg(c, fentry, k));
            }
            fprintf(out, "|->");
            display_ast(c, out, Z3_func_entry_get_value(c, fentry));
            fprintf(out, ")");
            Z3_func_entry_dec_ref(c, fentry);
        }
        if (num_entries > 0) {
            fprintf(out, ", ");
        }
        fprintf(out, "(else|->");
        func_else = Z3_func_interp_get_else(c, finterp);
        display_ast(c, out, func_else);
        fprintf(out, ")}\n");
        Z3_func_interp_dec_ref(c, finterp);
    }
}

/**
 \brief Custom model pretty printer.
 */
void display_model(Z3_context c, FILE * out, Z3_model m)
{
    unsigned num_constants;
    unsigned i;
    
    if (!m) return;
    
    num_constants = Z3_model_get_num_consts(c, m);
    for (i = 0; i < num_constants; i++) {
        Z3_symbol name;
        Z3_func_decl cnst = Z3_model_get_const_decl(c, m, i);
        Z3_ast a, v;
        Z3_bool ok;
        name = Z3_get_decl_name(c, cnst);
        display_symbol(c, out, name);
        fprintf(out, " = ");
        a = Z3_mk_app(c, cnst, 0, 0);
        v = a;
        ok = Z3_model_eval(c, m, a, 1, &v);
        display_ast(c, out, v);
        fprintf(out, "\n");
    }
    display_function_interpretations(c, out, m);
}



/***************************************************/
/*               make a new context                */
/***************************************************/

/**
 \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    /* printf("Error code: %d\n", e);
    exitf("incorrect use of Z3"); */
    char *error = NULL;
    
    switch(e)
    {
        case Z3_OK:
            error = "Z3_OK";
            break;
        case Z3_SORT_ERROR:
            error = "Z3_SORT_ERROR";
            break;
        case Z3_IOB:
            error = "Z3_IOB";
            break;
        case Z3_INVALID_ARG:
            error = "Z3_INVALID_ARG";
            break;
        case Z3_PARSER_ERROR:
            error = "Z3_PARSER_ERROR";
            break;
        case Z3_NO_PARSER:
            error = "Z3_NO_PARSER";
            break;
        case Z3_INVALID_PATTERN:
            error = "Z3_INVALID_PATTERN";
            break;
        case Z3_MEMOUT_FAIL:
            error = "Z3_MEMOUT_FAIL";
            break;
        case Z3_FILE_ACCESS_ERROR:
            error = "Z3_FILE_ACCESS_ERROR";
            break;
        case Z3_INTERNAL_FATAL:
            error = "Z3_INTERNAL_FATAL";
            break;
        case Z3_INVALID_USAGE:
            error = "Z3_INVALID_USAGE";
            break;
        case Z3_DEC_REF_ERROR:
            error = "Z3_DEC_REF_ERROR";
            break;
        case Z3_EXCEPTION:
            error = "Z3_EXCEPTION";
            break;
        default:
            error = "Z3 BUG: unknown error";
    }
    
    term_t t1 = PL_new_term_ref();
    t1 = PL_new_functor(PL_new_atom(error), 0);
    PL_raise_exception(t1);    /* raise the exception */
}

/**
 Create a configuration
 */
static foreign_t pl_mk_config()
{
    cfg = Z3_mk_config();
    return 1;
}

/**
 Delete a configuration
 */
static foreign_t pl_del_config()
{
    Z3_del_config(cfg);
    return 1;
}

/**
 Set a configuration parameter
 */
static foreign_t pl_set_param_value(term_t param, term_t value)
{
    char *par,*val;
    if (!PL_get_chars(param,&par,CVT_STRING))
        return PL_warning("z3_set_parameter_value/1: instantiation fault (parameter)");
    if (!PL_get_chars(value,&val,CVT_STRING))
        return PL_warning("z3_set_parameter_value/1: instantiation fault (value)");
    
    Z3_set_param_value(cfg,par,val);
    return 1;
}

/**
 Create a context with index ind using the current configuration
 Enable tracing to stderr and register standard error handler.
 */
static foreign_t pl_mk_context(term_t ind)
{
    int rval;
    
    if (cur<MAXCONS) {
        ctx[cur] = Z3_mk_context(cfg);
        Z3_set_error_handler(ctx[cur], error_handler);
        rval = PL_unify_integer(ind,cur);
        cur++;
    } else {
        return PL_warning("z3_mk_context/1: max contexts reached");
    }
    return rval;
}

/**
 Create a solver associated to the context with index ind
 */
static foreign_t pl_mk_solver(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_mk_solver/2: instantiation fault");

    z3s[i] = Z3_mk_solver(ctx[i]);
    Z3_solver_inc_ref(ctx[i], z3s[i]);

    return 1;
}

/**
 Delete a solver associated to the context with index ind
 */
static foreign_t pl_del_solver(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_del_solver/2: instantiation fault");

    Z3_solver_dec_ref(ctx[i], z3s[i]);
    
    return 1;
}


/**
 Delete a context with index ind
 */
static foreign_t pl_del_context(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
        return PL_warning("z3_del_context/1: instantiation fault");
    
    Z3_del_context(ctx[i]);
    
    return 1;
}

/**
 Create a backtracking point in the context with index ind
 */
static foreign_t pl_push(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_push/1: instantiation fault");
    
    Z3_solver_push(ctx[i],z3s[i]);
    
    return 1;
}

/**
 Backtrack one point in the context with index ind
 */
static foreign_t pl_pop(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_pop/1: instantiation fault");
    
    Z3_solver_pop(ctx[i],z3s[i],1);
    
    return 1;
}

/**
 Declares a list of integer variables
 */

Z3_ast var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    Z3_symbol s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

static foreign_t pl_mk_int_vars(term_t ind, term_t varlist)
{
    int i;
    
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_parse_string/2: instantiation fault (context)");
    
    term_t plvar = PL_new_term_ref();   /* the elements */
    term_t list = PL_copy_term_ref(varlist); /* copy (we modify list) */
    
    while( PL_get_list(list, plvar, list) )
    {
        char *varname;
        if (!PL_get_chars(plvar,&varname,CVT_STRING))
        return PL_warning("z3_mk_int_vars/2: instantiation fault");
        
        Z3_ast v = var(ctx[i], varname);
        names[i][numvar[i]] = Z3_mk_string_symbol(ctx[i], varname);
        decls[i][numvar[i]] = Z3_get_app_decl(ctx[i],  Z3_to_app(ctx[i], v));
        numvar[i]=numvar[i]+1;
    }
    
    return PL_get_nil(list);
    
}


/**
 Declares a new integer variable varname in context ind
 */
static foreign_t pl_assert_string(term_t ind, term_t plstr)
{
    Z3_error_code e;
    int i;
    
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_assert_string/2: instantiation fault (context)");
    
    char *z3string;
    if (!PL_get_chars(plstr,&z3string,CVT_STRING))
    return PL_warning("z3_assert_string/2: instantiation fault (string)");
    
    Z3_ast fs = Z3_parse_smtlib2_string(ctx[i], z3string, 0, 0, 0, numvar[i], names[i], decls[i]);
    printf("--asserted formula: %s\n", Z3_ast_to_string(ctx[i], fs));
    
    e = Z3_get_error_code(ctx[i]);
    if (e != Z3_OK) goto err;
    
    Z3_solver_assert(ctx[i], z3s[i], fs);
    return 1;
    
err:
    printf("Z3 error: %s.\n", Z3_get_error_msg(ctx[i], e));
    if (ctx[i] != NULL) {
        printf("Error message: '%s'.\n",Z3_get_parser_error(ctx[i]));
    }
    return 0;
}



/**
    Check the satisfiability of a context with index ind
 */
static foreign_t pl_check(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
        return PL_warning("z3_check/1: instantiation fault");
 
    Z3_bool result = Z3_solver_check(ctx[i],z3s[i]);
    
    Z3_model m = 0;
    
    int rval=1;
    
    switch (result) {
        case Z3_L_FALSE:
            printf("unsat\n");
            rval=0;
            break;
        case Z3_L_TRUE:
            printf("sat\n");
            break;
        case Z3_L_UNDEF:
            printf("unknown\n");
            break;
    }
    
     /* Z3_solver_reset(ctx[i],z3s[i]); */
    return rval;
}

/**
 Show the computed model for a context ind
 */
static foreign_t pl_print_model(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_get_model/1: instantiation fault");
    
    Z3_model m = 0;
    
    m = Z3_solver_get_model(ctx[i], z3s[i]);
    if (m) Z3_model_inc_ref(ctx[i], m);
    printf("MODEL:\n%s", Z3_model_to_string(ctx[i], m));
    
    return 1;
}

/**
 Show the computed model for an integer variable
 */
static foreign_t pl_get_model_intvar_eval(term_t ind, term_t varname, term_t varval)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_get_model_intvar_eval/3: instantiation fault (context)");
    
    char *vn;
    if (!PL_get_chars(varname,&vn,CVT_STRING))
    return PL_warning("z3_get_model_intvar_eval/3: instantiation fault (varname)");
    
    Z3_model m = 0;
    
    m = Z3_solver_get_model(ctx[i], z3s[i]);
    if (m) Z3_model_inc_ref(ctx[i], m);
    
    Z3_ast n = var(ctx[i], vn);
    Z3_ast v;
    
    int val;
    if (Z3_model_eval(ctx[i], m, n, 1, &v)) {
        Z3_get_numeral_int(ctx[i], v, &val);
    } else {
        exitf("failed to evaluate the variable");
    }
    
    int rval;
    rval = PL_unify_integer(varval, val);
    
    return rval;
}



/***************************************************/
/*         registered SWI Prolog predicates        */
/***************************************************/

install_t install()
{
    PL_register_foreign("z3_mk_config", 0, pl_mk_config, 0);
    PL_register_foreign("z3_del_config", 0, pl_del_config, 0);
    PL_register_foreign("z3_set_param_value", 2, pl_set_param_value, 0);
    PL_register_foreign("z3_mk_new_context", 1, pl_mk_context, 0);
    PL_register_foreign("z3_del_context", 1, pl_del_context, 0);
    PL_register_foreign("z3_mk_solver", 1, pl_mk_solver, 0);
    PL_register_foreign("z3_del_solver", 1, pl_del_solver, 0);
    PL_register_foreign("z3_push", 1, pl_push, 0);
    PL_register_foreign("z3_pop", 1, pl_pop, 0);
    PL_register_foreign("z3_mk_int_vars", 2, pl_mk_int_vars, 0);
    PL_register_foreign("z3_assert_string_", 2, pl_assert_string, 0);
    PL_register_foreign("z3_check", 1, pl_check, 0);
    PL_register_foreign("z3_print_model", 1, pl_print_model, 0);
    PL_register_foreign("z3_get_model_intvar_eval", 3, pl_get_model_intvar_eval, 0);

}
