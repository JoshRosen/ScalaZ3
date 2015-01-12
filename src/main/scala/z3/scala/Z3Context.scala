package z3.scala

import jnr.ffi.Pointer
import jnr.ffi.byref.IntByReference
import scala.collection.mutable.{Set=>MutableSet}
import java.math.BigInteger

object Z3Context {
  sealed abstract class ADTSortReference
  case class RecursiveType(index: Int) extends ADTSortReference
  case class RegularSort(sort: Z3Sort) extends ADTSortReference

  object AstPrintMode extends Enumeration {
    type AstPrintMode = Value
    val Z3_PRINT_SMTLIB_FULL, Z3_PRINT_LOW_LEVEL, Z3_PRINT_SMTLIB_COMPLIANT, Z3_PRINT_SMTLIB2_COMPLIANT = Value
  }
  import AstPrintMode._
}

sealed class Z3Context(val config: Z3Config) {
  val ptr: Pointer = Z3Wrapper.Z3_mk_context_rc(config.ptr)

  registerContext(ptr, this)

  val astQueue       = new Z3RefCountQueue[Z3ASTLike]()
  val astvectorQueue = new Z3RefCountQueue[Z3ASTVector]()
  val modelQueue     = new Z3RefCountQueue[Z3Model]()
  val solverQueue    = new Z3RefCountQueue[Z3Solver](5)
  val tacticQueue    = new Z3RefCountQueue[Z3Tactic]()

  def this(params : (String,Any)*) = this(new Z3Config(params : _*))

  private var deleted : Boolean = false
  override def finalize() : Unit = {
    if(!deleted) this.delete()
  }

  def delete() : Unit = {
    if(!deleted) {
      astQueue.clearQueue()
      modelQueue.clearQueue()
      solverQueue.clearQueue()
      astvectorQueue.clearQueue()
      tacticQueue.clearQueue()

      unregisterContext(this.ptr)

      Z3Wrapper.Z3_del_context(this.ptr)
      deleted = true
    }
  }

  def onError(code: Long): Nothing = {
    throw new Exception("Unexpected Z3 error (code="+code+")")
  }

  @deprecated("Use interrupt instead", "")
  def softCheckCancel() : Unit = {
    Z3Wrapper.Z3_interrupt(this.ptr)
  }

  override def toString : String = {
    Z3Wrapper.Z3_context_to_string(this.ptr)
  }

  def astToString(ast: Z3AST) : String = {
    Z3Wrapper.Z3_ast_to_string(this.ptr, ast.ptr)
  }

  def funcDeclToString(funcDecl: Z3FuncDecl) : String = {
    Z3Wrapper.Z3_func_decl_to_string(this.ptr, funcDecl.ptr)
  }

  def sortToString(sort: Z3Sort) : String = {
    Z3Wrapper.Z3_sort_to_string(this.ptr, sort.ptr)
  }

  def patternToString(pattern: Z3Pattern) : String = {
    Z3Wrapper.Z3_pattern_to_string(this.ptr, pattern.ptr)
  }

  def modelToString(model: Z3Model) : String = {
    Z3Wrapper.Z3_model_to_string(this.ptr, model.ptr)
  }

  def benchmarkToSMTLIBString(name : String, logic : String, status : String, attributes : String, assumptions : Seq[Z3AST], formula : Z3AST) : String = {
    Z3Wrapper.Z3_benchmark_to_smtlib_string(this.ptr, name, logic, status, attributes, assumptions.size, toPtrArray(assumptions), formula.ptr)
  }

  def updateParamValue(paramID: String, paramValue: String) : Unit = {
    Z3Wrapper.Z3_update_param_value(this.ptr, paramID, paramValue)
  }

  private val usedIntSymbols : MutableSet[Int] = MutableSet.empty
  private var lastUsed : Int = -1

  def mkIntSymbol(i: Int) : Z3Symbol = {
    usedIntSymbols += i
    new Z3Symbol(Z3Wrapper.Z3_mk_int_symbol(this.ptr, i), this)
  }

  def mkFreshIntSymbol : Z3Symbol = {
    var i = lastUsed + 1
    while(usedIntSymbols(i)) {
      i += 1
    }
    lastUsed = i
    mkIntSymbol(i)
  }

  private val usedStringSymbols : MutableSet[String] = MutableSet.empty
  def mkStringSymbol(s: String) : Z3Symbol = {
    usedStringSymbols += s
    new Z3Symbol(Z3Wrapper.Z3_mk_string_symbol(this.ptr, s), this)
  }

  def mkFreshStringSymbol(s: String) : Z3Symbol = {
    if(!usedStringSymbols(s)) {
      mkStringSymbol(s)
    } else {
      var i = 0
      while(usedStringSymbols(s + i)) {
        i += 1
      }
      mkStringSymbol(s + i)
    }
  }

  /*
  def isArrayValue(ast: Z3AST) : Option[Int] = {
    val numEntriesPtr = new Z3Wrapper.
    ()
    val result = Z3Wrapper.Z3_is_array_value(this.ptr, ast.ptr, numEntriesPtr)
    if (result) {
      Some(numEntriesPtr.value)
    } else {
      None
    }
  }

  @deprecated("use `getArrayValue' in `Z3Model' instead")
  def getArrayValue(ast: Z3AST) : Option[(Map[Z3AST, Z3AST], Z3AST)] = isArrayValue(ast) match {
    case None => None
    case Some(numEntries) => {
      // val indices = (0 until numEntries).map(_ => new Z3AST((new Pointer(0L)).ptr, this)).toList
      // val values  = (0 until numEntries).map(_ => new Z3AST((new Pointer(0L)).ptr, this)).toList
      val indArray = new Array[Pointer](numEntries)
      val valArray = new Array[Pointer](numEntries)
      val elseValuePtr = new Pointer(0L)

      // println("indices before : " + indArray.toList.mkString(", "))
      // println("values  before : " + valArray.toList.mkString(", "))
      // println("else    before : " + elseValuePtr.ptr)

      Z3Wrapper.Z3_get_array_value(this.ptr, ast.ptr, numEntries, indArray, valArray, elseValuePtr)

      // println("indices after : " + indArray.toList.mkString(", "))
      // println("values  after : " + valArray.toList.mkString(", "))
      // println("else    after : " + elseValuePtr.ptr)

      val elseValue = new Z3AST(elseValuePtr.ptr, this)
      val map = Map((indArray.map(new Z3AST(_, this)) zip valArray.map(new Z3AST(_, this))): _*)
      Some((map, elseValue))
    }
  }

  @deprecated("use `getSetValue' in `Z3Model' instead")
  def getSetValue(ast: Z3AST) : Option[Set[Z3AST]] = getArrayValue(ast) match {
    case None => None
    case Some((map, elseValue)) =>
      Some(map.filter(pair => getBoolValue(pair._2) == Some(true)).keySet.toSet)
  }
  */

  def isEqSort(s1: Z3Sort, s2: Z3Sort) : Boolean = {
    Z3Wrapper.Z3_is_eq_sort(this.ptr, s1.ptr, s2.ptr)
  }

  def mkUninterpretedSort(s: Z3Symbol) : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_uninterpreted_sort(this.ptr, s.ptr), this)
  }

  def mkUninterpretedSort(s : String) : Z3Sort = {
    mkUninterpretedSort(mkStringSymbol(s))
  }

  def mkBoolSort() : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_bool_sort(this.ptr), this)
  }

  def mkIntSort() : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_int_sort(this.ptr), this)
  }

  def mkRealSort() : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_real_sort(this.ptr), this)
  }
  
  import Z3Context.{ADTSortReference,RecursiveType,RegularSort}

  def mkADTSorts(defs: Seq[(String, Seq[String], Seq[Seq[(String,ADTSortReference)]])]) : Seq[(Z3Sort, Seq[Z3FuncDecl], Seq[Z3FuncDecl], Seq[Seq[Z3FuncDecl]])] = {
    val typeCount: Int = defs.size

    // the following big block builds the following three lists
    var symbolList:   List[Z3Symbol] = Nil
    var consListList: List[Pointer] = Nil
    var consScalaList: List[List[(Pointer,Int)]] = Nil // in the Scala list, we maintain number of fields

    for(tuple <- defs) yield {
      val (typeName, typeConstructorNames, typeConstructorArgs) = tuple
      val constructorCount: Int = typeConstructorNames.size
      if(constructorCount != typeConstructorArgs.size) {
        throw new IllegalArgumentException("sequence of constructor names should have the same size as sequence of constructor param lists, for type " + typeName)
      }

      val sym: Z3Symbol = mkStringSymbol(typeName)
      symbolList = sym :: symbolList

      val constructors = for((tcn, tca) <- (typeConstructorNames zip typeConstructorArgs)) yield {
        val consSym: Z3Symbol = mkStringSymbol(tcn)
        val testSym: Z3Symbol = mkStringSymbol("is" + tcn)
        val fieldSyms: Array[Pointer] = tca.map(p => mkStringSymbol(p._1).ptr).toArray
        val fieldSorts: Array[Pointer] = tca.map(p => p._2 match {
          case RecursiveType(idx) if idx >= typeCount => throw new IllegalArgumentException("index of recursive type is too big (" + idx + ") for field " + p._1 + " of type " + typeName)
          case RegularSort(srt) => srt.ptr
          case RecursiveType(_) => runtime.getMemoryManager.newPointer(0)
        }).toArray

        val fieldRefs: Array[Int] = tca.map(p => p._2 match {
          case RegularSort(_) => 0
          case RecursiveType(idx) => idx
        }).toArray

        val consPtr = Z3Wrapper.Z3_mk_constructor(this.ptr, consSym.ptr, testSym.ptr, fieldSyms.size, fieldSyms, fieldSorts, fieldRefs)
        (consPtr, fieldSyms.size)
      }

      val consArr = constructors.map(_._1).toArray
      val consList = Z3Wrapper.Z3_mk_constructor_list(this.ptr, consArr.length, consArr)
      consListList = consList :: consListList
      consScalaList = constructors.toList :: consScalaList
    }

    symbolList   = symbolList.reverse
    consListList = consListList.reverse
    consScalaList = consScalaList.reverse
    
    val newSorts: Array[Pointer] = {
      val arrPtr: Pointer = Z3Wrapper.Z3_mk_datatypes(this.ptr, typeCount, toPtrArray(symbolList), consListList.toArray)
      ptr.getNullTerminatedPointerArray(0)
    }

    consListList.foreach(cl => Z3Wrapper.Z3_del_constructor_list(this.ptr, cl))
    
    for((sort, consLst) <- (newSorts zip consScalaList)) yield {
      val zipped = for (cons <- consLst) yield {
        val consFunPtr = runtime.getMemoryManager.allocate(4)
        val testFunPtr = runtime.getMemoryManager.newPointer(0)

        val selectors: Array[Pointer] = if(cons._2 > 0) new Array[Pointer](cons._2) else null

        Z3Wrapper.Z3_query_constructor(this.ptr, cons._1, cons._2, consFunPtr, testFunPtr, selectors)

        val consFun = new Z3FuncDecl(consFunPtr, cons._2, this)
        val testFun = new Z3FuncDecl(testFunPtr, 1, this)
        (consFun, (testFun, if(cons._2 > 0) selectors.map(new Z3FuncDecl(_, 1, this)).toList else Nil))
      }

      val (consFuns, unzippedOnce) = zipped.unzip
      val (testFuns, selectorFunss) = unzippedOnce.unzip
  
      (new Z3Sort(sort, this), consFuns, testFuns, selectorFunss)
    }
  }

  def isEqAST(t1: Z3AST, t2: Z3AST) : Boolean = {
    Z3Wrapper.Z3_is_eq_ast(this.ptr, t1.ptr, t2.ptr)
  }

  def mkApp(funcDecl: Z3FuncDecl, args: Z3AST*) : Z3AST = {
    if(funcDecl.arity != args.size)
      throw new IllegalArgumentException("Calling mkApp with wrong number of arguments.")

    new Z3AST(Z3Wrapper.Z3_mk_app(this.ptr, funcDecl.ptr, args.size, toPtrArray(args)), this)
  }

  def isEqFuncDecl(fd1: Z3FuncDecl, fd2: Z3FuncDecl) : Boolean = {
    Z3Wrapper.Z3_is_eq_func_decl(this.ptr, fd1.ptr, fd2.ptr)
  }

  def mkConst(symbol: Z3Symbol, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_const(this.ptr, symbol.ptr, sort.ptr), this)
  }

  def mkConst(s: String, sort: Z3Sort) : Z3AST = {
    mkConst(mkStringSymbol(s), sort)
  }

  def mkIntConst(symbol: Z3Symbol) : Z3AST = {
    mkConst(symbol, mkIntSort)
  }

  def mkIntConst(s: String) : Z3AST = {
    mkIntConst(mkStringSymbol(s))
  }

  def mkBoolConst(symbol: Z3Symbol) : Z3AST = {
    mkConst(symbol, mkBoolSort)
  }

  def mkBoolConst(s: String) : Z3AST = {
    mkBoolConst(mkStringSymbol(s))
  }

  def mkFuncDecl(symbol: Z3Symbol, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = {
    new Z3FuncDecl(Z3Wrapper.Z3_mk_func_decl(this.ptr, symbol.ptr, domainSorts.size, toPtrArray(domainSorts), rangeSort.ptr), domainSorts.size, this)
  }

  def mkFuncDecl(symbol: Z3Symbol, domainSort: Z3Sort, rangeSort: Z3Sort) : Z3FuncDecl = {
    mkFuncDecl(symbol, Seq(domainSort), rangeSort)
  }

  def mkFuncDecl(symbol: String, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = {
    mkFuncDecl(mkStringSymbol(symbol), domainSorts, rangeSort)
  }

  def mkFuncDecl(symbol: String, domainSort: Z3Sort, rangeSort: Z3Sort) : Z3FuncDecl = {
    mkFuncDecl(mkStringSymbol(symbol), Seq(domainSort), rangeSort)
  }

  def mkFreshConst(prefix: String, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_fresh_const(this.ptr, prefix, sort.ptr), this)
  }

  def mkFreshIntConst(prefix: String) : Z3AST = {
    mkFreshConst(prefix, mkIntSort)
  }

  def mkFreshBoolConst(prefix: String) : Z3AST = {
    mkFreshConst(prefix, mkBoolSort)
  }

  def mkFreshFuncDecl(prefix: String, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = {
    new Z3FuncDecl(Z3Wrapper.Z3_mk_fresh_func_decl(this.ptr, prefix, domainSorts.size, toPtrArray(domainSorts), rangeSort.ptr), domainSorts.size, this)
  }

  def mkTrue() : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_true(this.ptr), this)
  }

  def mkFalse() : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_false(this.ptr), this)
  }

  def mkEq(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_eq(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkDistinct(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkDistinct needs at least one argument")
    } else if(args.size == 1) {
      mkTrue
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_distinct(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkNot(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_not(this.ptr, ast.ptr), this)
  }

  def mkITE(t1: Z3AST, t2: Z3AST, t3: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_ite(this.ptr, t1.ptr, t2.ptr, t3.ptr), this)
  }

  def mkIff(t1: Z3AST, t2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_iff(this.ptr, t1.ptr, t2.ptr), this)
  }

  def mkImplies(t1: Z3AST, t2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_implies(this.ptr, t1.ptr, t2.ptr), this)
  }

  def mkXor(t1: Z3AST, t2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_xor(this.ptr, t1.ptr, t2.ptr), this)
  }

  def mkAnd(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkAnd needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_and(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkOr(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkOr needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_or(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkAdd(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkAdd needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_add(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkMul(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkMul needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_mul(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkSub(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkSub needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_sub(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkUnaryMinus(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_unary_minus(this.ptr, ast.ptr), this)
  }

  def mkDiv(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_div(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkMod(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_mod(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkRem(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_rem(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkPower(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_power(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkLT(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_lt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkLE(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_le(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkGT(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_gt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkGE(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_ge(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkInt2Real(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_int2_real(this.ptr, ast.ptr), this)
  }

  def mkReal2Int(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_real2_int(this.ptr, ast.ptr), this)
  }

  def mkIsInt(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_is_int(this.ptr, ast.ptr), this)
  }

  def mkArraySort(domain: Z3Sort, range: Z3Sort) : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_array_sort(this.ptr, domain.ptr, range.ptr), this)
  }

  def mkSelect(array: Z3AST, index: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_select(this.ptr, array.ptr, index.ptr), this)
  }

  def mkStore(array: Z3AST, index: Z3AST, value: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_store(this.ptr, array.ptr, index.ptr, value.ptr), this)
  }

  def mkConstArray(sort: Z3Sort, value: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_const_array(this.ptr, sort.ptr, value.ptr), this)
  }

  def mkArrayDefault(array: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_array_default(this.ptr, array.ptr), this)
  }

  def mkTupleSort(name : Z3Symbol, sorts : Z3Sort*) : (Z3Sort,Z3FuncDecl,Seq[Z3FuncDecl]) = {
    require(sorts.size > 0)
    val sz = sorts.size
    val consPtr = runtime.getMemoryManager.newPointer(0)
    val projFuns = new Array[Pointer](sz)
    val fieldNames = sorts.map(s => mkFreshStringSymbol(name + "-field")).toArray
    val sortPtr = Z3Wrapper.Z3_mk_tuple_sort(this.ptr, name.ptr, sz, fieldNames.map(_.ptr), sorts.map(_.ptr).toArray, consPtr, projFuns)
    val newSort = new Z3Sort(sortPtr, this)
    val consFuncDecl = new Z3FuncDecl(consPtr, sz, this)
    val projFuncDecls = projFuns.map(ptr => new Z3FuncDecl(ptr, 1, this)).toSeq
    (newSort, consFuncDecl, projFuncDecls)
  }

  def mkTupleSort(name : String, sorts : Z3Sort*) : (Z3Sort,Z3FuncDecl,Seq[Z3FuncDecl]) = mkTupleSort(mkStringSymbol(name), sorts : _*)

  def mkSetSort(underlying: Z3Sort) : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_set_sort(this.ptr, underlying.ptr), this)
  }

  def mkEmptySet(sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_empty_set(this.ptr, sort.ptr), this)
  }

  def mkFullSet(sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_full_set(this.ptr, sort.ptr), this)
  }

  def mkSetAdd(set: Z3AST, elem: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_set_add(this.ptr, set.ptr, elem.ptr), this)
  }

  def mkSetDel(set: Z3AST, elem: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_set_del(this.ptr, set.ptr, elem.ptr), this)
  }

  def mkSetUnion(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkSetUnion needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_set_union(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkSetIntersect(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkSetIntersect needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.Z3_mk_set_intersect(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkSetDifference(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_set_difference(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkSetComplement(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_set_complement(this.ptr, ast.ptr), this)
  }

  def mkSetMember(elem: Z3AST, set: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_set_member(this.ptr, elem.ptr, set.ptr), this)
  }

  def mkSetSubset(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_set_subset(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkInt(value: Int, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_int(this.ptr, value, sort.ptr), this)
  }
  
  def mkReal(numerator: Int, denominator: Int) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_real(this.ptr, numerator, denominator), this)
  }

  def mkNumeral(value: String, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_numeral(this.ptr, value, sort.ptr), this)
  }

  def mkPattern(args: Z3AST*) : Z3Pattern = {
    new Z3Pattern(Z3Wrapper.Z3_mk_pattern(this.ptr, args.size, toPtrArray(args)), this)
  }

  def mkBound(index: Int, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bound(this.ptr, index, sort.ptr), this)
  }

  def mkForAll(weight: Int, patterns: Seq[Z3Pattern], decls: Seq[(Z3Symbol,Z3Sort)], body: Z3AST) : Z3AST = mkQuantifier(true, weight, patterns, decls, body)

  def mkExists(weight: Int, patterns: Seq[Z3Pattern], decls: Seq[(Z3Symbol,Z3Sort)], body: Z3AST) : Z3AST = mkQuantifier(false, weight, patterns, decls, body)

  def mkQuantifier(isForAll: Boolean, weight: Int, patterns: Seq[Z3Pattern], decls: Seq[(Z3Symbol,Z3Sort)], body: Z3AST) : Z3AST = {
    val (declSyms, declSorts) = decls.unzip
    new Z3AST(
      Z3Wrapper.Z3_mk_quantifier(
        this.ptr,
        isForAll,
        weight,
        patterns.size,
        toPtrArray(patterns),
        decls.size,
        toPtrArray(declSorts),
        toPtrArray(declSyms),
        body.ptr),
      this
    )
  }

  def mkBVSort(size: Int) : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_mk_bvsort(this.ptr, size), this)
  }

  def mkBVNot(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvnot(this.ptr, ast.ptr), this)
  }

  def mkBVRedAnd(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvred_and(this.ptr, ast.ptr), this)
  }

  def mkBVRedOr(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvred_or(this.ptr, ast.ptr), this)
  }

  def mkBVAnd(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvand(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVOr(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVXor(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvxor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVNand(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvnand(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVNor(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvnor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVXnor(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvxnor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVNeg(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvneg(this.ptr, ast.ptr), this)
  }

  def mkBVAdd(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvadd(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSub(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsub(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVMul(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvmul(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUdiv(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvudiv(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSdiv(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsdiv(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUrem(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvurem(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSrem(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsrem(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSmod(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsmod(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUlt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvult(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSlt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvslt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUle(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvule(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSle(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsle(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUgt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvugt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSgt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsgt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUge(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvuge(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSge(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvsge(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkConcat(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_concat(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkExtract(high: Int, low: Int, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_extract(this.ptr, high, low, ast.ptr), this)
  }

  def mkSignExt(extraSize: Int, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_sign_ext(this.ptr, extraSize, ast.ptr), this)
  }

  def mkZeroExt(extraSize: Int, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_zero_ext(this.ptr, extraSize, ast.ptr), this)
  }

  def mkBVShl(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvshl(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVLshr(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvlshr(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVAshr(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvashr(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkExtRotateLeft(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_ext_rotate_left(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkExtRotateRight(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_ext_rotate_right(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVAddNoOverflow(ast1: Z3AST, ast2: Z3AST, isSigned: Boolean) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_bvadd_no_overflow(this.ptr, ast1.ptr, ast2.ptr, isSigned), this)
  }

  def getSymbolKind(symbol: Z3Symbol) : Z3SymbolKind[_] = {
    Z3Wrapper.Z3_get_symbol_kind(this.ptr, symbol.ptr) match {
      case 0 => Z3IntSymbol(getSymbolInt(symbol))
      case 1 => Z3StringSymbol(getSymbolString(symbol))
      case other => error("Z3_get_symbol_kind returned an unknown value : " + other)
    }
  }

  private[z3] def getSymbolInt(symbol: Z3Symbol) : Int = {
    Z3Wrapper.Z3_get_symbol_int(this.ptr, symbol.ptr)
  }

  private[z3] def getSymbolString(symbol: Z3Symbol) : String = {
    Z3Wrapper.Z3_get_symbol_string(this.ptr, symbol.ptr)
  }

  def getASTKind(ast: Z3AST) : Z3ASTKind = {
    Z3Wrapper.Z3_get_astkind(this.ptr, ast.ptr) match {
      case 0 =>
        if (getSort(ast).isRealSort) getNumeralReal(ast)
        else getNumeralInt(ast)

      case 1 => {
        val numArgs = getAppNumArgs(ast)
        val args = (Seq.tabulate(numArgs)){ i => getAppArg(ast, i) }
        Z3AppAST(getAppDecl(ast, numArgs), args)
      }
      case 2 => {
        val index = getIndexValue(ast)
        Z3VarAST(index)
      }
      case 3 => {
        val body = getQuantifierBody(ast)
        val forall = isQuantifierForall(ast)
        val numVars = getQuantifierNumBound(ast)
        val varSymbols = (0 to numVars-1).map(getQuantifierBoundName(ast, _))
        val varNames = varSymbols.map(x => getSymbolKind(x) match { case Z3IntSymbol(x) => "#" + x.toString(); case Z3StringSymbol(s) => s})
        Z3QuantifierAST(forall, varNames, body)
      }
      case _ => Z3UnknownAST
    }
  }

  def getIndexValue(ast: Z3AST) : Int = {
    return Z3Wrapper.Z3_get_index_value(this.ptr, ast.ptr)
  }

  def isQuantifierForall(ast: Z3AST) : Boolean = {
    return Z3Wrapper.Z3_is_quantifier_forall(this.ptr, ast.ptr)
  }

  def getQuantifierBody(ast: Z3AST) : Z3AST = {
    return new Z3AST(Z3Wrapper.Z3_get_quantifier_body(this.ptr, ast.ptr), this)
  }

  def getQuantifierBoundName(ast: Z3AST, i: Int) : Z3Symbol = {
    return new Z3Symbol(Z3Wrapper.Z3_get_quantifier_bound_name(this.ptr, ast.ptr, i), this)
  }

  def getQuantifierNumBound(ast: Z3AST) : Int = {
    return Z3Wrapper.Z3_get_quantifier_num_bound(this.ptr, ast.ptr)
  }

  def getDeclKind(funcDecl: Z3FuncDecl) : Z3DeclKind.Value = {
    import Z3DeclKind._

    Z3Wrapper.Z3_get_decl_kind(this.ptr, funcDecl.ptr) match {
      case  0 => OpTrue 
      case  1 => OpFalse 
      case  2 => OpEq 
      case  3 => OpDistinct 
      case  4 => OpITE 
      case  5 => OpAnd 
      case  6 => OpOr 
      case  7 => OpIff 
      case  8 => OpXor 
      case  9 => OpNot 
      case 10 => OpImplies 
      case 11 => OpANum 
      case 12 => OpLE 
      case 13 => OpGE 
      case 14 => OpLT 
      case 15 => OpGT 
      case 16 => OpAdd 
      case 17 => OpSub 
      case 18 => OpUMinus 
      case 19 => OpMul 
      case 20 => OpDiv 
      case 21 => OpIDiv 
      case 22 => OpRem 
      case 23 => OpMod 
      case 24 => OpToReal 
      case 25 => OpToInt 
      case 26 => OpIsInt 
      case 27 => OpStore 
      case 28 => OpSelect 
      case 29 => OpConstArray 
      case 30 => OpArrayDefault 
      case 31 => OpArrayMap 
      case 32 => OpSetUnion 
      case 33 => OpSetIntersect 
      case 34 => OpSetDifference 
      case 35 => OpSetComplement 
      case 36 => OpSetSubset 
      case 37 => OpAsArray 
      case 1000 => OpUninterpreted
      case 9999 => Other 
      case other => error("Unhandled int code for Z3KindDecl: " + other)
    }
  }

  def getAppDecl(ast: Z3AST, arity: Int = -1) : Z3FuncDecl = {
    val ad = Z3Wrapper.Z3_get_app_decl(this.ptr, ast.ptr)
    val ary = if(arity > -1) arity else Z3Wrapper.Z3_get_domain_size(this.ptr, ad)
    new Z3FuncDecl(ad, ary, this)
  }

  private def getAppNumArgs(ast: Z3AST) : Int = {
    Z3Wrapper.Z3_get_app_num_args(this.ptr, ast.ptr)
  }

  private def getAppArg(ast: Z3AST, i: Int) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_get_app_arg(this.ptr, ast.ptr, i), this)
  }

  def getDeclName(fd: Z3FuncDecl) : Z3Symbol = {
    new Z3Symbol(Z3Wrapper.Z3_get_decl_name(this.ptr, fd.ptr), this)
  }

  // TODO arity
  def getDeclFuncDeclParameter(fd: Z3FuncDecl, idx: Int, arity: Int = 1) : Z3FuncDecl = {
    new Z3FuncDecl(Z3Wrapper.Z3_get_decl_func_decl_parameter(this.ptr, fd.ptr, idx), arity, this)
  }

  def getSort(ast: Z3AST) : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_get_sort(this.ptr, ast.ptr), this)
  }

  def getDomainSize(funcDecl: Z3FuncDecl) : Int = funcDecl.arity

  def getDomain(funcDecl: Z3FuncDecl, i: Int) : Z3Sort = {
    if(funcDecl.arity <= i)
      throw new IllegalArgumentException("Calling getDomain with too large index.")

    new Z3Sort(Z3Wrapper.Z3_get_domain(this.ptr, funcDecl.ptr, i), this)
  }

  def getRange(funcDecl: Z3FuncDecl) : Z3Sort = {
    new Z3Sort(Z3Wrapper.Z3_get_range(this.ptr, funcDecl.ptr), this)
  }

  def getNumeralInt(ast: Z3AST) : Z3NumeralIntAST = {
    val ip = new IntByReference()
    val res = Z3Wrapper.Z3_get_numeral_int(this.ptr, ast.ptr, ip)
    if(res)
      Z3NumeralIntAST(Some(ip.getValue))
    else
      Z3NumeralIntAST(None)
  }

  def getNumeralReal(ast: Z3AST) : Z3NumeralRealAST = {
    val numZ3AST = new Z3AST(Z3Wrapper.Z3_get_numerator(this.ptr, ast.ptr), this)
    val denZ3AST = new Z3AST(Z3Wrapper.Z3_get_denominator(this.ptr, ast.ptr), this)
    val num = new BigInt(new BigInteger(Z3Wrapper.Z3_get_numeral_string(this.ptr, numZ3AST.ptr)))
    val den = new BigInt(new BigInteger(Z3Wrapper.Z3_get_numeral_string(this.ptr, denZ3AST.ptr)))
    Z3NumeralRealAST(num, den)
  }

  def getBoolValue(ast: Z3AST) : Option[Boolean] = {
    val res = i2ob(Z3Wrapper.Z3_get_bool_value(this.ptr, ast.ptr))
    res
  }

  // This is deprecated, we don't want to go directly through Contexts for
  // this, but via Solver

  private lazy val globalSolver = mkSolver()

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def push() : Unit = {
    globalSolver.push()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def pop(numScopes : Int = 1) : Unit = {
    globalSolver.pop(numScopes)
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def getNumScopes() : Int = {
    globalSolver.getNumScopes()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def assertCnstr(ast: Z3AST) : Unit = {
    globalSolver.assertCnstr(ast)
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def assertCnstr(tree : dsl.Tree[dsl.BoolSort]) : Unit = {
    globalSolver.assertCnstr(tree.ast(this))
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def check() : Option[Boolean] = {
    globalSolver.check()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAndGetModel() : (Option[Boolean],Z3Model) = {
    globalSolver.checkAndGetModel()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAssumptions(assumptions: Z3AST*) : (Option[Boolean],Z3Model,Seq[Z3AST]) = {
    val res   = globalSolver.checkAssumptions(assumptions : _*)
    val model = if (res != Some(false)) globalSolver.getModel() else null
    val core  = if (res != Some(true)) globalSolver.getUnsatCore().toSeq else Seq()

    (res, model, core)
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAndGetAllModels(): Iterator[Z3Model] = {
    globalSolver.checkAndGetAllModels()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAndGetAllEventualModels(): Iterator[(Option[Boolean], Z3Model)] = {
    globalSolver.checkAndGetAllEventualModels()
  }

  @deprecated("You should use Z3Solver.getReasonUnknown", "")
  def getSearchFailure : Z3SearchFailure = {
    Z3Wrapper.Z3_get_search_failure(this.ptr) match {
      case 0 => Z3NoFailure
      case 1 => Z3Unknown
      case 2 => Z3Timeout
      case 3 => Z3MemoutWatermark
      case 4 => Z3Canceled
      case 5 => Z3NumConflicts
      case 6 => Z3IncompleteTheory
      case 7 => Z3Quantifiers
      case _ => Z3Timeout
    }
  }

  def mkLabel(symbol: Z3Symbol, polarity: Boolean, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_mk_label(this.ptr, symbol.ptr, polarity, ast.ptr), this)
  }

//  def getRelevantLabels : Z3Literals = {
//    new Z3Literals(Z3Wrapper.Z3_get_relevant_labels(this.ptr), this)
//  }

  def getRelevantLiterals : Z3Literals = {
    new Z3Literals(Z3Wrapper.Z3_get_relevant_literals(this.ptr), this)
  }

  def getGuessedLiterals : Z3Literals = {
    new Z3Literals(Z3Wrapper.Z3_get_guessed_literals(this.ptr), this)
  }

// in Z3Literals instead
//  def delLiterals(lbls: Z3Literals) : Unit = {
//    Z3Wrapper.Z3_del_literals(this.ptr, lbls.ptr)
//  }

  def getNumLiterals(lbls: Z3Literals) : Int = {
    Z3Wrapper.Z3_get_num_literals(this.ptr, lbls.ptr)
  }

//  def getLabelSymbol(lbls: Z3Literals, idx: Int) : Z3Symbol = {
//    new Z3Symbol(Z3Wrapper.Z3_get_label_symbol(this.ptr, lbls.ptr, idx), this)
//  }

  def getLiteral(lbls: Z3Literals, idx: Int) : Z3AST = {
    new Z3AST(Z3Wrapper.Z3_get_literal(this.ptr, lbls.ptr, idx), this)
  }

  def disableLiteral(lbls: Z3Literals, idx: Int) : Unit = {
    Z3Wrapper.Z3_disable_literal(this.ptr, lbls.ptr, idx)
  }

  def blockLiterals(lbls: Z3Literals) : Unit = {
    Z3Wrapper.Z3_block_literals(this.ptr, lbls.ptr)
  }

  // Parser interface
  private def parseSMTLIB(file: Boolean, str: String) : Unit = {
    if(file) {
      Z3Wrapper.Z3_parse_smtlib_file(this.ptr, str, 0, null, null, 0, null, null)
    } else {
      Z3Wrapper.Z3_parse_smtlib_string(this.ptr, str, 0, null, null, 0, null, null)
    }
  }
  private def parseSMTLIB2(file: Boolean, str: String) : Z3AST = {
    if(file) {
      new Z3AST(Z3Wrapper.Z3_parse_smtlib_2_file(this.ptr, str, 0, null, null, 0, null, null), this)
    } else {
      new Z3AST(Z3Wrapper.Z3_parse_smtlib_2_string(this.ptr, str, 0, null, null, 0, null, null), this)
    }
  }
  private def parseSMTLIB(file: Boolean, str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Unit = {
    val (sortNames, z3Sorts) = sorts.unzip
    val (declNames, z3Decls) = decls.unzip
    if(file) {
      Z3Wrapper.Z3_parse_smtlib_file(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls))
    } else {
      Z3Wrapper.Z3_parse_smtlib_string(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls))
    }
  }
  private def parseSMTLIB2(file: Boolean, str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Z3AST = {
    val (sortNames, z3Sorts) = sorts.unzip
    val (declNames, z3Decls) = decls.unzip
    if(file) {
      new Z3AST(Z3Wrapper.Z3_parse_smtlib_2_file(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls)), this)
    } else {
      new Z3AST(Z3Wrapper.Z3_parse_smtlib_2_string(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls)), this)
    }
  }

  /** Uses the SMT-LIB parser to read in a benchmark file.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBFile(fileName: String) : Unit = parseSMTLIB(true, fileName)

  /** Uses the SMT-LIB parser to read in a benchmark string.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBString(str: String) : Unit = parseSMTLIB(false, str)

  /** Uses the SMT-LIB parser to read in a benchmark file. The maps are used to override symbols that would otherwise be created by the parser.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBFile(fileName: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Unit = parseSMTLIB(true, fileName, sorts, decls)

  /** Uses the SMT-LIB parser to read in a benchmark string. The maps are used to override symbols that would otherwise be created by the parser.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBString(str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Unit = parseSMTLIB(false, str, sorts, decls)

  /** Uses the SMT-LIB 2 parser to read in a benchmark file.
   */
  def parseSMTLIB2File(fileName: String) : Z3AST = parseSMTLIB2(true, fileName)

  /** Uses the SMT-LIB 2 parser to read in a benchmark string.
   */
  def parseSMTLIB2String(str: String) : Z3AST = parseSMTLIB2(false, str)

  /** Uses the SMT-LIB 2 parser to read in a benchmark file. The maps are used to override symbols that would otherwise be created by the parser.
   */
  def parseSMTLIB2File(fileName: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Z3AST = parseSMTLIB2(true, fileName, sorts, decls)

  /** Uses the SMT-LIB 2 parser to read in a benchmark string. The maps are used to override symbols that would otherwise be created by the parser.
   */
  def parseSMTLIB2String(str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Z3AST = parseSMTLIB2(false, str, sorts, decls)

  /** Returns an iterator of the formulas created by the SMT-LIB parser. */
  def getSMTLIBFormulas : Iterator[Z3AST] = {
    val ctx = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.Z3_get_smtlib_num_formulas(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.Z3_get_smtlib_formula(ctx.ptr, returned), ctx)
        returned += 1
        toReturn
      }
    }
  }

  /** Returns an iterator of the assumptions created by the SMT-LIB parser. */
  def getSMTLIBAssumptions : Iterator[Z3AST] = {
    val ctx = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.Z3_get_smtlib_num_assumptions(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.Z3_get_smtlib_assumption(ctx.ptr, returned), ctx)
        returned += 1
        toReturn
      }
    }
  }

  /** Returns an iterator of the function and constant declarations created by the SMT-LIB parser. */
  def getSMTLIBDecls : Iterator[Z3FuncDecl] = {
    val ctx = this
    new Iterator[Z3FuncDecl] {
      val total : Int = Z3Wrapper.Z3_get_smtlib_num_decls(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3FuncDecl = {
        val fdPtr = Z3Wrapper.Z3_get_smtlib_decl(ctx.ptr, returned)
        val arity = Z3Wrapper.Z3_get_domain_size(ctx.ptr, fdPtr)
        val toReturn = new Z3FuncDecl(Z3Wrapper.Z3_get_smtlib_decl(ctx.ptr, returned), arity, ctx)
        returned += 1
        toReturn
      }
    }
  }

  /** Returns an iterator of the sorts created by the SMT-LIB parser. */
  def getSMTLIBSorts : Iterator[Z3Sort] = {
    val ctx = this
    new Iterator[Z3Sort] {
      val total : Int = Z3Wrapper.Z3_get_smtlib_num_sorts(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3Sort = {
        val toReturn = new Z3Sort(Z3Wrapper.Z3_get_smtlib_sort(ctx.ptr, returned), ctx)
        returned += 1
        toReturn
      }
    }
  }

  def substitute(ast : Z3AST, from : Array[Z3AST], to : Array[Z3AST]) : Z3AST = {
    if (from.length != to.length)
      throw new IllegalArgumentException("from and to must have the same length");
    return new Z3AST(Z3Wrapper.Z3_substitute(this.ptr, ast.ptr, from.length, from.map(_.ptr), to.map(_.ptr)), this);
  }

  def setAstPrintMode(printMode : Z3Context.AstPrintMode.AstPrintMode) = {
    var mode : Int = 0
    printMode match {
      case Z3Context.AstPrintMode.Z3_PRINT_SMTLIB_FULL => mode = 0
      case Z3Context.AstPrintMode.Z3_PRINT_LOW_LEVEL => mode = 1
      case Z3Context.AstPrintMode.Z3_PRINT_SMTLIB_COMPLIANT => mode = 2
      case Z3Context.AstPrintMode.Z3_PRINT_SMTLIB2_COMPLIANT => mode = 3
    }
    Z3Wrapper.Z3_set_ast_print_mode(this.ptr, mode);
  }

  def simplifyAst(ast : Z3AST) : Z3AST = {
    return new Z3AST(Z3Wrapper.Z3_simplify(this.ptr, ast.ptr), this);
  }

  def mkForAllConst(weight: Int, patterns: Seq[Z3Pattern], bounds: Seq[Z3AST], body: Z3AST) : Z3AST = mkQuantifierConst(true, weight, patterns, bounds, body)

  def mkExistsConst(weight: Int, patterns: Seq[Z3Pattern], bounds: Seq[Z3AST], body: Z3AST) : Z3AST = mkQuantifierConst(false, weight, patterns, bounds, body)

  def mkQuantifierConst(isForAll: Boolean, weight: Int, patterns: Seq[Z3Pattern], bounds: Seq[Z3AST], body: Z3AST) : Z3AST = {
    new Z3AST(
      Z3Wrapper.Z3_mk_quantifier_const(
        this.ptr,
        isForAll,
        weight,
        bounds.size,
        toPtrArray(bounds),
        patterns.size,
        toPtrArray(patterns),
        body.ptr),
      this
    )
  }

  def mkTactic(name: String) : Z3Tactic = {
    return new Z3Tactic(Z3Wrapper.Z3_mk_tactic(this.ptr, name), this)
  }

  def mkTacticAndThen(tactic1: Z3Tactic, tactic2: Z3Tactic) : Z3Tactic = {
    return new Z3Tactic(Z3Wrapper.Z3_tactic_and_then(this.ptr, tactic1.ptr, tactic2.ptr), this)
  }

  def mkSolver() : Z3Solver = {
    new Z3Solver(Z3Wrapper.Z3_mk_solver(this.ptr), this)
  }

  def mkSolverFromTactic(tactic: Z3Tactic) : Z3Solver = {
    new Z3Solver(Z3Wrapper.Z3_mk_solver_from_tactic(this.ptr, tactic.ptr), this)
  }

  def interrupt() = {
    Z3Wrapper.Z3_interrupt(this.ptr)
  }

  /** Returns the last error issued by the SMT-LIB parser. */
  def getSMTLIBError : String = Z3Wrapper.Z3_get_smtlib_error(this.ptr)
}
