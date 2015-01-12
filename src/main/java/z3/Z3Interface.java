package z3;


import jnr.ffi.Pointer;
import jnr.ffi.annotations.Out;
import jnr.ffi.byref.IntByReference;
import jnr.ffi.byref.PointerByReference;

public interface Z3Interface {
  Pointer Z3_mk_config();
  void Z3_open_log(String name);
  void Z3_del_config(Pointer configPtr);
  void Z3_set_param_value(Pointer configPtr, String paramID, String paramValue);
  Pointer Z3_mk_context(Pointer configPtr);
  Pointer Z3_mk_context_rc(Pointer configPtr);
  void Z3_inc_ref(Pointer contextPtr, Pointer ptr);
  void Z3_dec_ref(Pointer contextPtr, Pointer ptr);
  void Z3_interrupt(Pointer contextPtr);
  void Z3_del_context(Pointer contextPtr);
  void Z3_toggle_warning_messages(boolean enabled);
  void Z3_update_param_value(Pointer contextPtr, String paramID, String paramValue);
  Pointer Z3_mk_int_symbol(Pointer contextPtr, int i);
  Pointer Z3_mk_string_symbol(Pointer contextPtr, String s);
  boolean Z3_is_eq_sort(Pointer contextPtr, Pointer sortPtr1, Pointer sortPtr2);
  Pointer Z3_mk_uninterpreted_sort(Pointer contextPtr, Pointer symbolPtr);
  Pointer Z3_mk_bool_sort(Pointer contextPtr);
  Pointer Z3_mk_int_sort(Pointer contextPtr);
  Pointer Z3_mk_real_sort(Pointer contextPtr);
  // ...

  Pointer Z3_mk_constructor(Pointer contextPtr, Pointer symbolPtr1, Pointer symbolPtr2, int numFields, Pointer[] fieldNames, Pointer[] sorts, int[] sortRefs);
  void Z3_query_constructor(Pointer contextPtr, Pointer constructorPtr, int numFields, Pointer constructor, Pointer tester, Pointer[] selectors);
  // void delConstructor(Pointer contextPtr, Pointer constructorPtr);
  // Pointer mkDatatype(Pointer contextPtr, Pointer symbolPtr, int numConstructors, Pointer[] constructors);
  Pointer Z3_mk_constructor_list(Pointer contextPtr, int numConstructors, Pointer[] constructors);
  void Z3_del_constructor_list(Pointer contextPtr, Pointer constructorListPtr);
  // returns an array containing the new sorts.
  Pointer Z3_mk_datatypes(Pointer contextPtr, int numSorts, Pointer[] sortNames, Pointer[] constructorLists);

  // ...
  boolean Z3_is_eq_ast(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  // ...
  Pointer Z3_mk_app(Pointer contextPtr, Pointer funcDeclPtr, int numArgs, Pointer[] args);
  boolean Z3_is_eq_func_decl(Pointer contextPtr, Pointer fdPtr1, Pointer fdPtr2);
  Pointer Z3_mk_const(Pointer contextPtr, Pointer symbolPtr, Pointer sortPtr);
  Pointer Z3_mk_func_decl(Pointer contextPtr, Pointer symbolPtr, int domainSize, Pointer[] domainSortPtrs, Pointer rangeSortPtr);
  Pointer Z3_mk_fresh_const(Pointer contextPtr, String prefix, Pointer sortPtr);
  Pointer Z3_mk_fresh_func_decl(Pointer contextPtr, String prefix, int domainSize, Pointer[] domainSortPtrs, Pointer rangeSortPtr);

  // ...
  Pointer Z3_mk_true(Pointer contextPtr);
  Pointer Z3_mk_false(Pointer contextPtr);
  Pointer Z3_mk_eq(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_distinct(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer Z3_mk_not(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_ite(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, Pointer astPtr3);
  Pointer Z3_mk_iff(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_implies(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_xor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_and(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer Z3_mk_or(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer Z3_mk_add(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer Z3_mk_mul(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer Z3_mk_sub(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer Z3_mk_unary_minus(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_div(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_div2(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_mod(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_rem(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_power(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_lt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_le(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_gt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_ge(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_int2_real(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_real2_int(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_is_int(Pointer contextPtr, Pointer astPtr);
  // ...

  Pointer Z3_mk_array_sort(Pointer contextPtr, Pointer domainSortPtr, Pointer rangeSortPtr);
  Pointer Z3_mk_select(Pointer contextPtr, Pointer astPtrArr, Pointer astPtrInd);
  Pointer Z3_mk_store(Pointer contextPtr, Pointer astPtrArr, Pointer astPtrInd, Pointer astPtrVal);
  Pointer Z3_mk_const_array(Pointer contextPtr, Pointer sortPtr, Pointer astPtrVal);
  Pointer Z3_mk_array_default(Pointer contextPtr, Pointer astPtrArr);

  Pointer Z3_mk_tuple_sort(Pointer contextPtr, Pointer symPtr, int numFields, Pointer[] fieldNames, Pointer[] fieldSorts, Pointer constructor, Pointer[] projFuns);

  Pointer Z3_mk_set_sort(Pointer contextPtr, Pointer sortPtr);
  Pointer Z3_mk_empty_set(Pointer contextPtr, Pointer sortPtr);
  Pointer Z3_mk_full_set(Pointer contextPtr, Pointer sortPtr);
  Pointer Z3_mk_set_add(Pointer contextPtr, Pointer setPtr, Pointer elemPtr);
  Pointer Z3_mk_set_del(Pointer contextPtr, Pointer setPtr, Pointer elemPtr);
  Pointer Z3_mk_set_union(Pointer contextPtr, int argCount, Pointer[] args);
  Pointer Z3_mk_set_intersect(Pointer contextPtr, int argCount, Pointer[] args);
  Pointer Z3_mk_set_difference(Pointer contextPtr, Pointer setPtr1, Pointer setPtr2);
  Pointer Z3_mk_set_complement(Pointer contextPtr, Pointer setPtr);
  Pointer Z3_mk_set_member(Pointer contextPtr, Pointer elemPtr, Pointer setPtr);
  Pointer Z3_mk_set_subset(Pointer contextPtr, Pointer setPtr1, Pointer setPtr2);
  // ...
  Pointer Z3_mk_int(Pointer contextPtr, int v, Pointer sortPtr);
  Pointer Z3_mk_real(Pointer contextPtr, int num, int den);
  Pointer Z3_mk_numeral(Pointer contextPtr, String numeral, Pointer sortPtr);
  // ...
  Pointer Z3_mk_pattern(Pointer contextPtr, int numPatterns, Pointer[] terms);
  Pointer Z3_mk_bound(Pointer contextPtr, int index, Pointer sortPtr);
  Pointer Z3_mk_quantifier(Pointer contextPtr, boolean isForAll, int weight, int numPatterns, Pointer[] patterns, int numDecls, Pointer[] declSorts, Pointer[] declNames, Pointer body);
  Pointer Z3_mk_quantifier_const(Pointer contextPtr, boolean isForAll, int weight, int numBounds, Pointer[] bounds, int numPatterns, Pointer[] patterns, Pointer body);
  // ...

  // Bit vector fun
  Pointer Z3_mk_bvsort(Pointer contextPtr, int size);
  Pointer Z3_mk_bvnot(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_bvred_and(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_bvred_or(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_bvand(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvxor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvnand(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvnor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvxnor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvneg(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_bvadd(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsub(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvmul(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvudiv(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsdiv(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvurem(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsrem(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsmod(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvult(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvslt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvule(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsle(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvugt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsgt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvuge(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsge(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_concat(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_extract(Pointer contextPtr, int high, int low, Pointer astPtr);
  Pointer Z3_mk_sign_ext(Pointer contextPtr, int i, Pointer astPtr);
  Pointer Z3_mk_zero_ext(Pointer contextPtr, int i, Pointer astPtr);
  Pointer Z3_mk_repeat(Pointer contextPtr, int i, Pointer astPtr);
  Pointer Z3_mk_bvshl(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvlshr(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvashr(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_rotate_left(Pointer contextPtr, int i, Pointer astPtr);
  Pointer Z3_mk_rotate_right(Pointer contextPtr, int i, Pointer astPtr);
  Pointer Z3_mk_ext_rotate_left(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_ext_rotate_right(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_int2_bv(Pointer contextPtr, int size, Pointer astPtr);
  Pointer Z3_mk_bv2_int(Pointer contextPtr, Pointer astPtr, boolean isSigned);
  Pointer Z3_mk_bvadd_no_overflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, boolean isSigned);
  Pointer Z3_mk_bvadd_no_underflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsub_no_underflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, boolean isSigned);
  Pointer Z3_mk_bvsub_no_overflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvsdiv_no_overflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer Z3_mk_bvneg_no_overflow(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_mk_bvmul_no_overflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, boolean isSigned);
  Pointer Z3_mk_bvmul_no_underflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);

  int Z3_get_bvsort_size(Pointer contextPtr, Pointer sortPtr);

  // Returns one of the following values:
  // 0 - Z3_INT_SYMBOL
  // 1 - Z3_STRING_SYMBOL
  // ? - ???
  int Z3_get_symbol_kind(Pointer contextPtr, Pointer symbolPtr);
  int Z3_get_symbol_int(Pointer contextPtr, Pointer symbolPtr);
  String Z3_get_symbol_string(Pointer contextPtr, Pointer symbolPtr);
  // Returns one of the following values:
  //  0 - Z3_NUMERAL_AST
  //  1 - Z3_APP_AST
  //  2 - Z3_VAR_AST
  //  3 - Z3_QUANTIFIER_AST
  //  4 - Z3_UNKNOWN_AST
  // -1 - otherwise (should not happen)
  int Z3_get_astkind(Pointer contextPtr, Pointer astPtr);

  //  0 - OpTrue
  //  1 - OpFalse
  //  2 - OpEq
  //  3 - OpDistinct
  //  4 - OpITE
  //  5 - OpAnd
  //  6 - OpOr
  //  7 - OpIff
  //  8 - OpXor
  //  9 - OpNot
  // 10 - OpImplies
  // 11 - OpANum
  // 12 - OpLE
  // 13 - OpGE
  // 14 - OpLT
  // 15 - OpGT
  // 16 - OpAdd
  // 17 - OpSub
  // 18 - OpUMinus
  // 19 - OpMul
  // 20 - OpDiv
  // 21 - OpIDiv
  // 22 - OpRem
  // 23 - OpMod
  // 24 - OpToReal
  // 25 - OpToInt
  // 26 - OpIsInt
  // 27 - OpStore
  // 28 - OpSelect
  // 29 - OpConstArray
  // 30 - OpArrayDefault
  // 31 - OpArrayMap
  // 32 - OpSetUnion
  // 33 - OpSetIntersect
  // 34 - OpSetDifference
  // 35 - OpSetComplement
  // 36 - OpSetSubset
  // 37 - OpAsArray

  // 1000 - OpUninterpreted

  // 9999 - Other
  int Z3_get_decl_kind(Pointer contextPtr, Pointer funcDeclPtr);
  // ...
  Pointer Z3_get_app_decl(Pointer contextPtr, Pointer astPtr);
  int Z3_get_app_num_args(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_get_app_arg(Pointer contextPtr, Pointer astPtr, int i);
  // ...
  Pointer Z3_get_decl_name(Pointer contextPtr, Pointer funcDeclPtr);
  // ...
  Pointer Z3_get_decl_func_decl_parameter(Pointer contextPtr, Pointer funcDeclPtr, int idx);
  // ...
  Pointer Z3_get_sort(Pointer contextPtr, Pointer astPtr);
  int  Z3_get_domain_size(Pointer contextPtr, Pointer funcDeclPtr);
  Pointer Z3_get_domain(Pointer contextPtr, Pointer funcDeclPtr, int i);
  Pointer Z3_get_range(Pointer contextPtr, Pointer funcDeclPtr);
  // ...
  boolean Z3_get_numeral_int(Pointer contextPtr, Pointer astPtr, @Out IntByReference intPointer);
  String Z3_get_numeral_string(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_get_numerator(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_get_denominator(Pointer contextPtr, Pointer astPtr);
  boolean Z3_is_algebraic_number(Pointer contextPtr, Pointer astPtr);

  // ...
  int Z3_get_bool_value(Pointer contextPtr, Pointer astPtr);


  // Returns one of the following values:
  // 0 - Z3_NO_FAILURE       The last search was successful
  // 1 - Z3_UNKNOWN          Undocumented failure reason
  // 2 - Z3_TIMEOUT          Timeout
  // 3 - Z3_MEMOUT_WATERMARK Search hit a memory high-watermak limit
  // 4 - Z3_CANCELED         External cancel flag was set
  // 5 - Z3_NUM_CONFLICTS    Maximum number of conflicts was reached
  // 6 - Z3_THEORY           Theory is incomplete
  // 7 - Z3_QUANTIFIERS      Logical context contains universal quantifiers
  // ? - ????
  int Z3_get_search_failure(Pointer contextPtr);

  void Z3_del_model(Pointer contextPtr, Pointer modelPtr);
  void Z3_model_inc_ref(Pointer contextPtr, Pointer modelPtr);
  void Z3_model_dec_ref(Pointer contextPtr, Pointer modelPtr);
  // decprecated
  boolean Z3_eval(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, Pointer ast);
  boolean Z3_model_eval(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, boolean completion, @Out PointerByReference newAst);
  int Z3_get_model_num_constants(Pointer contextPtr, Pointer modelPtr);
  Pointer Z3_get_model_constant(Pointer contextPtr, Pointer modelPtr, int i);
  boolean Z3_is_array_value(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, @Out IntByReference numEntries);
  void Z3_get_array_value(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, int numEntries, Pointer[] indices, Pointer[] values, Pointer elseValue);
  int Z3_get_model_num_funcs(Pointer contextPtr, Pointer modelPtr);
  Pointer Z3_get_model_func_decl(Pointer contextPtr, Pointer modelPtr, int i);
  int Z3_get_model_func_num_entries(Pointer contextPtr, Pointer modelPtr, int i);
  int Z3_get_model_func_entry_num_args(Pointer contextPtr, Pointer modelPtr, int i, int j);
  Pointer Z3_get_model_func_entry_arg(Pointer contextPtr, Pointer modelPtr, int i, int j, int k);
  Pointer Z3_get_model_func_entry_value(Pointer contextPtr, Pointer modelPtr, int i, int j);
  Pointer Z3_get_model_func_else(Pointer contextPtr, Pointer modelPtr, int i);

  Pointer Z3_mk_label(Pointer contextPtr, Pointer symbolPtr, boolean polarity, Pointer astPtr);
  Pointer Z3_get_relevant_labels(Pointer contextPtr);
  Pointer Z3_get_relevant_literals(Pointer contextPtr);
  Pointer Z3_get_guessed_literals(Pointer contextPtr);
  void Z3_del_literals(Pointer contextPtr, Pointer lbls);
  int  Z3_get_num_literals(Pointer contextPtr, Pointer lbls);
  Pointer Z3_get_label_symbol(Pointer contextPtr, Pointer lbls, int idx);
  Pointer Z3_get_literal(Pointer contextPtr, Pointer lbls, int idx);

  boolean Z3_is_quantifier_forall(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_get_quantifier_body(Pointer contextPtr, Pointer astPtr);
  Pointer Z3_get_quantifier_bound_name(Pointer contextPtr, Pointer astPtr, int i);
  int Z3_get_quantifier_num_bound(Pointer contextPtr, Pointer astPtr);
  int Z3_get_index_value(Pointer contextPtr, Pointer astPtr);

  void Z3_disable_literal(Pointer contextPtr, Pointer lbls, int idx);
  void Z3_block_literals(Pointer contextPtr, Pointer lbls);

  // These are the side-effect versions...
  void Z3_print_ast(Pointer contextPtr, Pointer astPtr);
  void Z3_print_model(Pointer contextPtr, Pointer modelPtr);
  void Z3_print_context(Pointer contextPtr);
  // ...and these return strings.
  String Z3_ast_to_string(Pointer contextPtr, Pointer astPtr);
  String Z3_func_decl_to_string(Pointer contextPtr, Pointer funcDeclPtr);
  String Z3_sort_to_string(Pointer contextPtr, Pointer sortPtr);
  String Z3_pattern_to_string(Pointer contextPtr, Pointer patternPtr);
  String Z3_model_to_string(Pointer contextPtr, Pointer modelPtr);
  String Z3_context_to_string(Pointer contextPtr);
  String Z3_benchmark_to_smtlib_string(Pointer contextPtr, String name, String logic, String status, String attributes, int numAssumptions, Pointer[] assumptions, Pointer formulaPtr);

  // The following is related to the theory plugins.
  // TODO TODO TODO (josh)
  //private HashMap<Long,AbstractTheoryProxy> tpmap = new HashMap<Long,AbstractTheoryProxy>();

  Pointer Z3_mk_theory(Pointer ctxPtr, String name);
  // This is not a call to a Z3 function...
  void Z3_set_theory_callbacks(Pointer thyPtr, AbstractTheoryProxy atp, boolean setDelete, boolean setReduceEq, boolean setReduceApp, boolean setReduceDistinct, boolean setNewApp, boolean setNewElem, boolean setInitSearch, boolean setPush, boolean setPop, boolean setRestart, boolean setReset, boolean setFinalCheck, boolean setNewEq, boolean setNewDiseq, boolean setNewAssignment, boolean setNewRelevant);
  Pointer Z3_theory_mk_sort(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr);
  Pointer Z3_theory_mk_value(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr, Pointer sortPtr);
  Pointer Z3_theory_mk_constant(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr, Pointer sortPtr);
  Pointer Z3_theory_mk_func_decl(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr, int domainSize, Pointer[] domainSorts, Pointer rangeSort);
  void Z3_theory_assert_axiom(Pointer thyPtr, Pointer astPtr);
  void Z3_theory_assume_eq(Pointer thyPtr, Pointer t1Ptr, Pointer t2Ptr);
  void Z3_theory_enable_axiom_simplification(Pointer thyPtr, boolean flag);
  Pointer Z3_theory_get_eq_croot(Pointer thyPtr, Pointer astPtr);
  Pointer Z3_theory_get_eq_cnext(Pointer thyPtr, Pointer astPtr);
  int Z3_theory_get_num_parents(Pointer thyPtr, Pointer astPtr);
  Pointer Z3_theory_get_parent(Pointer thyPtr, Pointer astPtr, int i);
  boolean Z3_theory_is_value(Pointer thyPtr, Pointer astPtr);
  boolean Z3_theory_is_decl(Pointer thyPtr, Pointer declPtr);
  int Z3_theory_get_num_elems(Pointer thyPtr);
  Pointer Z3_theory_get_elem(Pointer thyPtr, int i);
  int Z3_theory_get_num_apps(Pointer thyPtr);
  Pointer Z3_theory_get_app(Pointer thyPtr, int i);

  // Parser interface
  void Z3_parse_smtlib_string(Pointer ctxPtr, String str, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  void Z3_parse_smtlib_file(Pointer ctxPtr, String fileName, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  Pointer Z3_parse_smtlib_2_string(Pointer ctxPtr, String str, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  Pointer Z3_parse_smtlib_2_file(Pointer ctxPtr, String fileName, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  int Z3_get_smtlib_num_formulas(Pointer contextPtr);
  Pointer Z3_get_smtlib_formula(Pointer contextPtr, int i);
  int Z3_get_smtlib_num_assumptions(Pointer contextPtr);
  Pointer Z3_get_smtlib_assumption(Pointer contextPtr, int i);
  int Z3_get_smtlib_num_decls(Pointer contextPtr);
  Pointer Z3_get_smtlib_decl(Pointer contextPtr, int i);
  int Z3_get_smtlib_num_sorts(Pointer contextPtr);
  Pointer Z3_get_smtlib_sort(Pointer contextPtr, int i);
  String Z3_get_smtlib_error(Pointer contextPtr);

  // various
  Pointer Z3_substitute(Pointer contextPtr, Pointer astPtr, int numExprs, Pointer[] from, Pointer[] to);
  void Z3_set_ast_print_mode(Pointer contextPtr, int mode);
  Pointer Z3_simplify(Pointer contextPtr, Pointer astPtr);

  // tactics and solvers
  Pointer Z3_mk_tactic(Pointer contextPtr, String name);
  Pointer Z3_tactic_and_then(Pointer contextPtr, Pointer tactic1Ptr, Pointer tactic2Ptr);
  Pointer Z3_mk_solver(Pointer contextPtr);
  Pointer Z3_mk_solver_from_tactic(Pointer contextPtr, Pointer tacticPtr);
  void Z3_tactic_inc_ref(Pointer contextPtr, Pointer tacticPtr);
  void Z3_tactic_dec_ref(Pointer contextPtr, Pointer tacticPtr);

  void Z3_solver_push(Pointer contextPtr, Pointer solverPtr);
  void Z3_solver_pop(Pointer contextPtr, Pointer solverPtr, int numScopes);
  void Z3_solver_assert(Pointer contextPtr, Pointer solverPtr, Pointer astPtr);
  void Z3_solver_reset(Pointer contextPtr, Pointer solverPtr);
  int Z3_solver_check(Pointer contextPtr, Pointer solverPtr);
  Pointer Z3_solver_get_model(Pointer contextPtr, Pointer solverPtr);
  Pointer Z3_solver_get_proof(Pointer contextPtr, Pointer solverPtr);
  void Z3_solver_inc_ref(Pointer contextPtr, Pointer solverPtr);
  void Z3_solver_dec_ref(Pointer contextPtr, Pointer solverPtr);
  Pointer Z3_solver_get_assertions(Pointer contextPtr, Pointer solverPtr);
  Pointer Z3_solver_get_unsat_core(Pointer contextPtr, Pointer solverPtr);
  int Z3_solver_get_num_scopes(Pointer contextPtr, Pointer solverPtr);
  int Z3_solver_check_assumptions(Pointer contextPtr, Pointer solverPtr, int numAssumptions, Pointer[] assumptions);
  String Z3_solver_get_reason_unknown(Pointer contextPtr, Pointer solverPtr);
  String Z3_solver_to_string(Pointer contextPtr, Pointer solverPtr);

  // AST Vector
  void Z3_ast_vector_inc_ref(Pointer contextPtr, Pointer vectorPtr);
  void Z3_ast_vector_dec_ref(Pointer contextPtr, Pointer vectorPtr);
  int Z3_ast_vector_size(Pointer contextPtr, Pointer vectorPtr);
  Pointer Z3_ast_vector_get(Pointer contextPtr, Pointer vectorPtr, int i);
  void Z3_ast_vector_set(Pointer contextPtr, Pointer vectorPtr, int i, Pointer astPtr);

  // Error handling
  // Yet to come...
  // void registerErrorHandler(Pointer contextPtr, AbstractErrorHandler handler);

  // Miscellaneous
  void Z3_get_version(IntByReference major, IntByReference minor, IntByReference buildNumber, IntByReference revisionNumber);
  void Z3_reset_memory();

  // DEPRECATED API
  void Z3_push(Pointer contextPtr);
  void Z3_pop(Pointer contextPtr, int numScopes);
  int Z3_get_num_scopes(Pointer contextPtr);
  void Z3_assert_cnstr(Pointer contextPtr, Pointer astPtr);
  int Z3_check(Pointer contextPtr);
  int Z3_check_and_get_model(Pointer contextPtr, Pointer model);
  int Z3_check_assumptions(Pointer contextPtr, int numAssumptions, Pointer[] assumptions, Pointer model, int coreSizeIn, IntByReference coreSizeOut, Pointer[] core);
}
