package z3;


import jnr.ffi.provider.IntPointer;
import jnr.ffi.Pointer;

public interface Z3Interface {
  Pointer Z3_mk_config();
  void openLog(String name);
  void delConfig(Pointer configPtr);
  void setParamValue(Pointer configPtr, String paramID, String paramValue);
  Pointer mkContext(Pointer configPtr);
  Pointer mkContextRC(Pointer configPtr);
  void incRef(Pointer contextPtr, Pointer ptr);
  void decRef(Pointer contextPtr, Pointer ptr);
  void interrupt(Pointer contextPtr);
  void delContext(Pointer contextPtr);
  void toggleWarningMessages(boolean enabled);
  void updateParamValue(Pointer contextPtr, String paramID, String paramValue);
  Pointer mkIntSymbol(Pointer contextPtr, int i);
  Pointer mkStringSymbol(Pointer contextPtr, String s);
  boolean isEqSort(Pointer contextPtr, Pointer sortPtr1, Pointer sortPtr2);
  Pointer mkUninterpretedSort(Pointer contextPtr, Pointer symbolPtr);
  Pointer mkBoolSort(Pointer contextPtr);
  Pointer mkIntSort(Pointer contextPtr);
  Pointer mkRealSort(Pointer contextPtr);
  // ...

  Pointer mkConstructor(Pointer contextPtr, Pointer symbolPtr1, Pointer symbolPtr2, int numFields, Pointer[] fieldNames, Pointer[] sorts, int[] sortRefs);
  void queryConstructor(Pointer contextPtr, Pointer constructorPtr, int numFields, Pointer constructor, Pointer tester, Pointer[] selectors);
  // void delConstructor(Pointer contextPtr, Pointer constructorPtr);
  // Pointer mkDatatype(Pointer contextPtr, Pointer symbolPtr, int numConstructors, Pointer[] constructors);
  Pointer mkConstructorList(Pointer contextPtr, int numConstructors, Pointer[] constructors);
  void delConstructorList(Pointer contextPtr, Pointer constructorListPtr);
  // returns an array containing the new sorts.
  Pointer[] mkDatatypes(Pointer contextPtr, int numSorts, Pointer[] sortNames, Pointer[] constructorLists);

  // ...
  boolean isEqAST(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  // ...
  Pointer mkApp(Pointer contextPtr, Pointer funcDeclPtr, int numArgs, Pointer[] args);
  boolean isEqFuncDecl(Pointer contextPtr, Pointer fdPtr1, Pointer fdPtr2);
  Pointer mkConst(Pointer contextPtr, Pointer symbolPtr, Pointer sortPtr);
  Pointer mkFuncDecl(Pointer contextPtr, Pointer symbolPtr, int domainSize, Pointer[] domainSortPtrs, Pointer rangeSortPtr);
  Pointer mkFreshConst(Pointer contextPtr, String prefix, Pointer sortPtr);
  Pointer mkFreshFuncDecl(Pointer contextPtr, String prefix, int domainSize, Pointer[] domainSortPtrs, Pointer rangeSortPtr);

  // ...
  Pointer mkTrue(Pointer contextPtr);
  Pointer mkFalse(Pointer contextPtr);
  Pointer mkEq(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkDistinct(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer mkNot(Pointer contextPtr, Pointer astPtr);
  Pointer mkITE(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, Pointer astPtr3);
  Pointer mkIff(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkImplies(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkXor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkAnd(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer mkOr(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer mkAdd(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer mkMul(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer mkSub(Pointer contextPtr, int numArgs, Pointer[] args);
  Pointer mkUnaryMinus(Pointer contextPtr, Pointer astPtr);
  Pointer mkDiv(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkDiv2(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkMod(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkRem(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkPower(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkLT(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkLE(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkGT(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkGE(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkInt2Real(Pointer contextPtr, Pointer astPtr);
  Pointer mkReal2Int(Pointer contextPtr, Pointer astPtr);
  Pointer mkIsInt(Pointer contextPtr, Pointer astPtr);
  // ...

  Pointer mkArraySort(Pointer contextPtr, Pointer domainSortPtr, Pointer rangeSortPtr);
  Pointer mkSelect(Pointer contextPtr, Pointer astPtrArr, Pointer astPtrInd);
  Pointer mkStore(Pointer contextPtr, Pointer astPtrArr, Pointer astPtrInd, Pointer astPtrVal);
  Pointer mkConstArray(Pointer contextPtr, Pointer sortPtr, Pointer astPtrVal);
  Pointer mkArrayDefault(Pointer contextPtr, Pointer astPtrArr);

  Pointer mkTupleSort(Pointer contextPtr, Pointer symPtr, int numFields, Pointer[] fieldNames, Pointer[] fieldSorts, Pointer constructor, Pointer[] projFuns);

  Pointer mkSetSort(Pointer contextPtr, Pointer sortPtr);
  Pointer mkEmptySet(Pointer contextPtr, Pointer sortPtr);
  Pointer mkFullSet(Pointer contextPtr, Pointer sortPtr);
  Pointer mkSetAdd(Pointer contextPtr, Pointer setPtr, Pointer elemPtr);
  Pointer mkSetDel(Pointer contextPtr, Pointer setPtr, Pointer elemPtr);
  Pointer mkSetUnion(Pointer contextPtr, int argCount, Pointer[] args);
  Pointer mkSetIntersect(Pointer contextPtr, int argCount, Pointer[] args);
  Pointer mkSetDifference(Pointer contextPtr, Pointer setPtr1, Pointer setPtr2);
  Pointer mkSetComplement(Pointer contextPtr, Pointer setPtr);
  Pointer mkSetMember(Pointer contextPtr, Pointer elemPtr, Pointer setPtr);
  Pointer mkSetSubset(Pointer contextPtr, Pointer setPtr1, Pointer setPtr2);
  // ...
  Pointer mkInt(Pointer contextPtr, int v, Pointer sortPtr);
  Pointer mkReal(Pointer contextPtr, int num, int den);
  Pointer mkNumeral(Pointer contextPtr, String numeral, Pointer sortPtr);
  // ...
  Pointer mkPattern(Pointer contextPtr, int numPatterns, Pointer[] terms);
  Pointer mkBound(Pointer contextPtr, int index, Pointer sortPtr);
  Pointer mkQuantifier(Pointer contextPtr, boolean isForAll, int weight, int numPatterns, Pointer[] patterns, int numDecls, Pointer[] declSorts, Pointer[] declNames, Pointer body);
  Pointer mkQuantifierConst(Pointer contextPtr, boolean isForAll, int weight, int numBounds, Pointer[] bounds, int numPatterns, Pointer[] patterns, Pointer body);
  // ...

  // Bit vector fun
  Pointer mkBVSort(Pointer contextPtr, int size);
  Pointer mkBVNot(Pointer contextPtr, Pointer astPtr);
  Pointer mkBVRedAnd(Pointer contextPtr, Pointer astPtr);
  Pointer mkBVRedOr(Pointer contextPtr, Pointer astPtr);
  Pointer mkBVAnd(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVOr(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVXor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVNand(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVNor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVXnor(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVNeg(Pointer contextPtr, Pointer astPtr);
  Pointer mkBVAdd(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSub(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVMul(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVUdiv(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSdiv(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVUrem(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSrem(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSmod(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVUlt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSlt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVUle(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSle(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVUgt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSgt(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVUge(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSge(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkConcat(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkExtract(Pointer contextPtr, int high, int low, Pointer astPtr);
  Pointer mkSignExt(Pointer contextPtr, int i, Pointer astPtr);
  Pointer mkZeroExt(Pointer contextPtr, int i, Pointer astPtr);
  Pointer mkRepeat(Pointer contextPtr, int i, Pointer astPtr);
  Pointer mkBVShl(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVLshr(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVAshr(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkRotateLeft(Pointer contextPtr, int i, Pointer astPtr);
  Pointer mkRotateRight(Pointer contextPtr, int i, Pointer astPtr);
  Pointer mkExtRotateLeft(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkExtRotateRight(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkInt2BV(Pointer contextPtr, int size, Pointer astPtr);
  Pointer mkBV2Int(Pointer contextPtr, Pointer astPtr, boolean isSigned);
  Pointer mkBVAddNoOverflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, boolean isSigned);
  Pointer mkBVAddNoUnderflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSubNoUnderflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, boolean isSigned);
  Pointer mkBVSubNoOverflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVSdivNoOverflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);
  Pointer mkBVNegNoOverflow(Pointer contextPtr, Pointer astPtr);
  Pointer mkBVMulNoOverflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2, boolean isSigned);
  Pointer mkBVMulNoUnderflow(Pointer contextPtr, Pointer astPtr1, Pointer astPtr2);

  int getBVSortSize(Pointer contextPtr, Pointer sortPtr);

  // Returns one of the following values:
  // 0 - Z3_INT_SYMBOL
  // 1 - Z3_STRING_SYMBOL
  // ? - ???
  int getSymbolKind(Pointer contextPtr, Pointer symbolPtr);
  int getSymbolInt(Pointer contextPtr, Pointer symbolPtr);
  String getSymbolString(Pointer contextPtr, Pointer symbolPtr);
  // Returns one of the following values:
  //  0 - Z3_NUMERAL_AST
  //  1 - Z3_APP_AST
  //  2 - Z3_VAR_AST
  //  3 - Z3_QUANTIFIER_AST
  //  4 - Z3_UNKNOWN_AST
  // -1 - otherwise (should not happen)
  int getASTKind(Pointer contextPtr, Pointer astPtr);

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
  int getDeclKind(Pointer contextPtr, Pointer funcDeclPtr);
  // ...
  Pointer getAppDecl(Pointer contextPtr, Pointer astPtr);
  int getAppNumArgs(Pointer contextPtr, Pointer astPtr);
  Pointer getAppArg(Pointer contextPtr, Pointer astPtr, int i);
  // ...
  Pointer getDeclName(Pointer contextPtr, Pointer funcDeclPtr);
  // ...
  Pointer getDeclFuncDeclParameter(Pointer contextPtr, Pointer funcDeclPtr, int idx);
  // ...
  Pointer getSort(Pointer contextPtr, Pointer astPtr);
  int  getDomainSize(Pointer contextPtr, Pointer funcDeclPtr);
  Pointer getDomain(Pointer contextPtr, Pointer funcDeclPtr, int i);
  Pointer getRange(Pointer contextPtr, Pointer funcDeclPtr);
  // ...
  boolean getNumeralInt(Pointer contextPtr, Pointer astPtr, Pointer IntPointer);
  String getNumeralString(Pointer contextPtr, Pointer astPtr);
  Pointer getNumerator(Pointer contextPtr, Pointer astPtr);
  Pointer getDenominator(Pointer contextPtr, Pointer astPtr);
  boolean isAlgebraicNumber(Pointer contextPtr, Pointer astPtr);

  // ...
  int getBoolValue(Pointer contextPtr, Pointer astPtr);


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
  int getSearchFailure(Pointer contextPtr);

  void delModel(Pointer contextPtr, Pointer modelPtr);
  void modelIncRef(Pointer contextPtr, Pointer modelPtr);
  void modelDecRef(Pointer contextPtr, Pointer modelPtr);
  // decprecated
  boolean eval(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, Pointer ast);
  boolean modelEval(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, Pointer ast, boolean completion);
  int getModelNumConstants(Pointer contextPtr, Pointer modelPtr);
  Pointer getModelConstant(Pointer contextPtr, Pointer modelPtr, int i);
  boolean isArrayValue(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, IntPointer numEntries);
  void getArrayValue(Pointer contextPtr, Pointer modelPtr, Pointer astPtr, int numEntries, Pointer[] indices, Pointer[] values, Pointer elseValue);
  int getModelNumFuncs(Pointer contextPtr, Pointer modelPtr);
  Pointer getModelFuncDecl(Pointer contextPtr, Pointer modelPtr, int i);
  int getModelFuncNumEntries(Pointer contextPtr, Pointer modelPtr, int i);
  int getModelFuncEntryNumArgs(Pointer contextPtr, Pointer modelPtr, int i, int j);
  Pointer getModelFuncEntryArg(Pointer contextPtr, Pointer modelPtr, int i, int j, int k);
  Pointer getModelFuncEntryValue(Pointer contextPtr, Pointer modelPtr, int i, int j);
  Pointer getModelFuncElse(Pointer contextPtr, Pointer modelPtr, int i);

  Pointer mkLabel(Pointer contextPtr, Pointer symbolPtr, boolean polarity, Pointer astPtr);
  Pointer getRelevantLabels(Pointer contextPtr);
  Pointer getRelevantLiterals(Pointer contextPtr);
  Pointer getGuessedLiterals(Pointer contextPtr);
  void delLiterals(Pointer contextPtr, Pointer lbls);
  int  getNumLiterals(Pointer contextPtr, Pointer lbls);
  Pointer getLabelSymbol(Pointer contextPtr, Pointer lbls, int idx);
  Pointer getLiteral(Pointer contextPtr, Pointer lbls, int idx);

  boolean isQuantifierForall(Pointer contextPtr, Pointer astPtr);
  Pointer getQuantifierBody(Pointer contextPtr, Pointer astPtr);
  Pointer getQuantifierBoundName(Pointer contextPtr, Pointer astPtr, int i);
  int getQuantifierNumBound(Pointer contextPtr, Pointer astPtr);
  int getIndexValue(Pointer contextPtr, Pointer astPtr);

  void disableLiteral(Pointer contextPtr, Pointer lbls, int idx);
  void blockLiterals(Pointer contextPtr, Pointer lbls);

  // These are the side-effect versions...
  void printAST(Pointer contextPtr, Pointer astPtr);
  void printModel(Pointer contextPtr, Pointer modelPtr);
  void printContext(Pointer contextPtr);
  // ...and these return strings.
  String astToString(Pointer contextPtr, Pointer astPtr);
  String funcDeclToString(Pointer contextPtr, Pointer funcDeclPtr);
  String sortToString(Pointer contextPtr, Pointer sortPtr);
  String patternToString(Pointer contextPtr, Pointer patternPtr);
  String modelToString(Pointer contextPtr, Pointer modelPtr);
  String contextToString(Pointer contextPtr);
  String benchmarkToSMTLIBString(Pointer contextPtr, String name, String logic, String status, String attributes, int numAssumptions, Pointer[] assumptions, Pointer formulaPtr);

  // The following is related to the theory plugins.
  // TODO TODO TODO (josh)
  //private HashMap<Long,AbstractTheoryProxy> tpmap = new HashMap<Long,AbstractTheoryProxy>();

  Pointer mkTheory(Pointer ctxPtr, String name);
  // This is not a call to a Z3 function...
  void setTheoryCallbacks(Pointer thyPtr, AbstractTheoryProxy atp, boolean setDelete, boolean setReduceEq, boolean setReduceApp, boolean setReduceDistinct, boolean setNewApp, boolean setNewElem, boolean setInitSearch, boolean setPush, boolean setPop, boolean setRestart, boolean setReset, boolean setFinalCheck, boolean setNewEq, boolean setNewDiseq, boolean setNewAssignment, boolean setNewRelevant);
  Pointer theoryMkSort(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr);
  Pointer theoryMkValue(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr, Pointer sortPtr);
  Pointer theoryMkConstant(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr, Pointer sortPtr);
  Pointer theoryMkFuncDecl(Pointer ctxPtr, Pointer thyPtr, Pointer symPtr, int domainSize, Pointer[] domainSorts, Pointer rangeSort);
  void theoryAssertAxiom(Pointer thyPtr, Pointer astPtr);
  void theoryAssumeEq(Pointer thyPtr, Pointer t1Ptr, Pointer t2Ptr);
  void theoryEnableAxiomSimplification(Pointer thyPtr, boolean flag);
  Pointer theoryGetEqCRoot(Pointer thyPtr, Pointer astPtr);
  Pointer theoryGetEqCNext(Pointer thyPtr, Pointer astPtr);
  int theoryGetNumParents(Pointer thyPtr, Pointer astPtr);
  Pointer theoryGetParent(Pointer thyPtr, Pointer astPtr, int i);
  boolean theoryIsValue(Pointer thyPtr, Pointer astPtr);
  boolean theoryIsDecl(Pointer thyPtr, Pointer declPtr);
  int theoryGetNumElems(Pointer thyPtr);
  Pointer theoryGetElem(Pointer thyPtr, int i);
  int theoryGetNumApps(Pointer thyPtr);
  Pointer theoryGetApp(Pointer thyPtr, int i);

  // Parser interface
  void parseSMTLIBString(Pointer ctxPtr, String str, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  void parseSMTLIBFile(Pointer ctxPtr, String fileName, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  Pointer parseSMTLIB2String(Pointer ctxPtr, String str, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  Pointer parseSMTLIB2File(Pointer ctxPtr, String fileName, int numSorts, Pointer[] sortNames, Pointer[] sorts, int numDecls, Pointer[] declNames, Pointer[] decls);
  int getSMTLIBNumFormulas(Pointer contextPtr);
  Pointer getSMTLIBFormula(Pointer contextPtr, int i);
  int getSMTLIBNumAssumptions(Pointer contextPtr);
  Pointer getSMTLIBAssumption(Pointer contextPtr, int i);
  int getSMTLIBNumDecls(Pointer contextPtr);
  Pointer getSMTLIBDecl(Pointer contextPtr, int i);
  int getSMTLIBNumSorts(Pointer contextPtr);
  Pointer getSMTLIBSort(Pointer contextPtr, int i);
  String getSMTLIBError(Pointer contextPtr);

  // various
  Pointer substitute(Pointer contextPtr, Pointer astPtr, int numExprs, Pointer[] from, Pointer[] to);
  void setAstPrintMode(Pointer contextPtr, int mode);
  Pointer simplify(Pointer contextPtr, Pointer astPtr);

  // tactics and solvers
  Pointer mkTactic(Pointer contextPtr, String name);
  Pointer tacticAndThen(Pointer contextPtr, Pointer tactic1Ptr, Pointer tactic2Ptr);
  Pointer mkSolver(Pointer contextPtr);
  Pointer mkSolverFromTactic(Pointer contextPtr, Pointer tacticPtr);
  void tacticIncRef(Pointer contextPtr, Pointer tacticPtr);
  void tacticDecRef(Pointer contextPtr, Pointer tacticPtr);

  void solverPush(Pointer contextPtr, Pointer solverPtr);
  void solverPop(Pointer contextPtr, Pointer solverPtr, int numScopes);
  void solverAssertCnstr(Pointer contextPtr, Pointer solverPtr, Pointer astPtr);
  void solverReset(Pointer contextPtr, Pointer solverPtr);
  int solverCheck(Pointer contextPtr, Pointer solverPtr);
  Pointer solverGetModel(Pointer contextPtr, Pointer solverPtr);
  Pointer solverGetProof(Pointer contextPtr, Pointer solverPtr);
  void solverIncRef(Pointer contextPtr, Pointer solverPtr);
  void solverDecRef(Pointer contextPtr, Pointer solverPtr);
  Pointer solverGetAssertions(Pointer contextPtr, Pointer solverPtr);
  Pointer solverGetUnsatCore(Pointer contextPtr, Pointer solverPtr);
  int solverGetNumScopes(Pointer contextPtr, Pointer solverPtr);
  int solverCheckAssumptions(Pointer contextPtr, Pointer solverPtr, int numAssumptions, Pointer[] assumptions);
  String solverGetReasonUnknown(Pointer contextPtr, Pointer solverPtr);
  String solverToString(Pointer contextPtr, Pointer solverPtr);

  // AST Vector
  void astvectorIncRef(Pointer contextPtr, Pointer vectorPtr);
  void astvectorDecRef(Pointer contextPtr, Pointer vectorPtr);
  int astvectorSize(Pointer contextPtr, Pointer vectorPtr);
  Pointer astvectorGet(Pointer contextPtr, Pointer vectorPtr, int i);
  void astvectorSet(Pointer contextPtr, Pointer vectorPtr, int i, Pointer astPtr);

  // Error handling
  // Yet to come...
  // void registerErrorHandler(Pointer contextPtr, AbstractErrorHandler handler);

  // Miscellaneous
  void getVersion(IntPointer major, IntPointer minor, IntPointer buildNumber, IntPointer revisionNumber);
  void resetMemory();

  // DEPRECATED API
  void push(Pointer contextPtr);
  void pop(Pointer contextPtr, int numScopes);
  int getNumScopes(Pointer contextPtr);
  void assertCnstr(Pointer contextPtr, Pointer astPtr);
  int check(Pointer contextPtr);
  int checkAndGetModel(Pointer contextPtr, Pointer model);
  int checkAssumptions(Pointer contextPtr, int numAssumptions, Pointer[] assumptions, Pointer model, int coreSizeIn, IntPointer coreSizeOut, Pointer[] core);
}